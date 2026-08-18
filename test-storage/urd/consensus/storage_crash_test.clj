(ns urd.consensus.storage-crash-test
  "urd's durability barrier, against konserve's own crash simulator.

  `sim.cljc` is urd's NETWORK simulator, complementing kabel. This is the
  storage half, and it is not urd's to write: konserve ships
  `konserve.simulation.crash`, which models the six crash points along the
  write path -- from SQLite/RocksDB/CrashMonkey, where every reported crash bug
  reproduced after an fsync-like call -- deterministically, with no RNG, and
  explicitly so that downstream projects can test against it.

  The stack under test is the real one:

      urd DurableStore  (stores/konserve.cljc, k/append + k/reduce-log)
        konserve DefaultStore
          CrashAwareBackingStore

  ## The two questions

  1. When a write fails, does urd hear about it, and is the log left clean?
     A torn record here is worse than a lost one: `restore` folds the log to
     rebuild the algorithm's state, so a half-written record is a node that
     comes back holding something no one ever wrote.

  2. When urd is TOLD a `:durable? true` write succeeded, does it survive?
     That is the entire content of the barrier. Every algorithm that gates a
     `commit` behind `persist-then` -- Tendermint, Bullshark, SCP -- is relying
     on this sentence being true.

  Not in CI: `konserve.simulation.*` is not in a released konserve (checked
  against 0.9.372), so this needs `{:local/root \"../konserve\"}`, exactly as
  the datahike ledger does. `bin/test-all` runs it."
  (:require [clojure.test :refer [deftest testing is]]
            [clojure.core.async :refer [<!!]]
            [konserve.simulation.crash :as crash]
            [konserve.impl.defaults :as defaults]
            [konserve.impl.storage-layout :as sl]
            [konserve.serializers :as ser]
            [urd.consensus.store :as store]
            [urd.consensus.stores.konserve :as kstore]))

(defn- urd-store-on
  "urd's `DurableStore` over a konserve DefaultStore over `backing`.

  Re-connectable: a crash is a new process, so recovery means building a fresh
  store on the same backing rather than reusing the object that died."
  [backing]
  (let [ks (defaults/connect-default-store
            backing
            {:opts {:sync? false}
             :config {:default-serializer :FressianSerializer
                      :serializers {:FressianSerializer (ser/fressian-serializer)}}
             :buffer-size 8192})]
    (kstore/konserve-store
     (if (instance? clojure.core.async.impl.channels.ManyToManyChannel ks)
       (<!! ks)
       ks))))

(defn- fresh []
  (let [info (crash/create-crash-aware-store)]
    (sl/-create-store (:backing info) {:sync? true})
    info))

(defn- writes-in [restored] (mapv :writes (:writes restored)))

(deftest a-crash-at-any-point-in-the-write-path-leaves-no-torn-record
  (testing "all six crash points, one at a time

           The invariant is all-or-nothing. `restore` folds the log to rebuild
           an algorithm's durable state, so a half-written record is not a lost
           write -- it is a node that comes back holding something nobody ever
           wrote, which is strictly worse and much harder to notice.

           Every point is also checked to REPORT the failure, because urd's
           barrier now fail-stops on a failed durable write, and it can only do
           that if `write!` says so. A store that swallowed this would produce
           a node that silently stopped committing."
    (doseq [point [:after-write-header :after-write-meta :after-write-value
                   :after-sync :after-atomic-move :after-sync-store]]
      (let [{:keys [backing crash-point-atom state-atom]} (fresh)
            st (urd-store-on backing)]
        (is (true? (<!! (store/write! st {:writes {:a 1} :durable? true}))))
        (is (true? (<!! (store/write! st {:writes {:b 2} :durable? true}))))

        (crash/set-crash-point! crash-point-atom point)
        (let [result (<!! (store/write! st {:writes {:c 3} :durable? true}))]
          (is (instance? Throwable result)
              (str point ": the failure must reach urd, or the barrier cannot
                   fail-stop on it"))

          (crash/simulate-crash! state-atom)
          (crash/clear-crash-point! crash-point-atom)

          (let [restored (<!! (store/restore (urd-store-on backing)))]
            (is (not (instance? Throwable restored))
                (str point ": the store must reopen after a crash"))
            (is (= [{:a 1} {:b 2}] (writes-in restored))
                (str point ": exactly the records that succeeded -- no torn
                     record, nothing partial, nothing invented"))))))))

(deftest a-durable-write-urd-was-told-succeeded-survives-a-crash
  (testing "the entire content of the barrier

           `persist-then` with `:durable? true` promises that nothing gated
           goes out until the record survives a crash. Tendermint, Bullshark
           and SCP all put `commit` in that gate. If an acknowledged write can
           vanish, every one of them can commit something and then come back
           having forgotten it -- which is the equivocation their whole design
           is built to prevent.

           So: write, be told it succeeded, crash WITHOUT any injected fault,
           and look."
    (let [{:keys [backing state-atom]} (fresh)
          st (urd-store-on backing)]
      (doseq [i (range 5)]
        (is (true? (<!! (store/write! st {:writes {:i i} :durable? true})))))

      (crash/simulate-crash! state-atom)

      (let [restored (<!! (store/restore (urd-store-on backing)))]
        (is (= (mapv (fn [i] {:i i}) (range 5)) (writes-in restored))
            "every acknowledged write is still there after the crash")
        (is (= {:i 4} (:durable restored))
            "and the merged view a restarting algorithm reads agrees with the
             log it was folded from")))))

(deftest the-log-restores-in-the-order-it-was-written
  (testing "`restore` hands back an ORDERED log, not a merged snapshot, because
            an append-only log is the only thing that can express
            `truncate-from` -- and Raft's replay depends on a later append at a
            lower index overwriting rather than unioning. Order surviving a
            crash is therefore part of the contract, not a detail."
    (let [{:keys [backing state-atom]} (fresh)
          st (urd-store-on backing)]
      (doseq [i (range 20)]
        (<!! (store/write! st {:writes {:n i} :durable? true})))
      (crash/simulate-crash! state-atom)
      (let [restored (<!! (store/restore (urd-store-on backing)))]
        (is (= (mapv (fn [i] {:n i}) (range 20)) (writes-in restored)))))))

(deftest the-acknowledgement-is-exactly-where-durability-begins
  (testing "what makes the durability test above non-vacuous

           If konserve acknowledged before syncing, 'an acknowledged write
           survives a crash' would be a coin flip rather than a contract. It
           does not: after an acknowledged write there is NOTHING pending, so
           the fsync has already happened by the time urd is told. That is the
           whole justification for `persist-then` being a barrier rather than a
           notification.

           What this deliberately does NOT assert is the fate of a write that
           was issued and not waited on. Its contract is that it MAY be lost,
           and whether it actually is depends on whether the writer go-loop got
           to it first -- a race. The first version of this test asserted it
           was lost, won the race in a probe, lost it in the suite, and would
           have been a flake shipped by someone who had spent all day removing
           them."
    (let [{:keys [backing state-atom]} (fresh)
          st (urd-store-on backing)]
      (is (true? (<!! (store/write! st {:writes {:acked 1} :durable? true}))))
      (is (zero? (count (crash/get-pending-data state-atom)))
          "nothing pending once the write is acknowledged -- the fsync happened
           BEFORE urd was told, which is what makes the barrier meaningful")
      (is (pos? (count (crash/get-synced-data state-atom)))
          "and it is on the synced side, not merely absent from both")

      (crash/simulate-crash! state-atom)

      (let [restored (<!! (store/restore (urd-store-on backing)))]
        (is (= [{:acked 1}] (writes-in restored))
            "the acknowledged write is there, and nothing else was invented")))))

(deftest an-unacknowledged-write-may-be-lost-and-never-corrupts
  (testing "the other side of the boundary, stated as the contract actually
            states it

           A write that was issued and not waited on may or may not survive --
           that is what `:durable? true` promises about the ACKNOWLEDGEMENT and
           nothing about the issue. The property that must hold either way is
           that the log is a PREFIX of what was written: the unacked record is
           present or absent, never half-present, and never in the wrong place.

           Run repeatedly, because which side of the race we land on varies and
           both are legal."
    (dotimes [_ 8]
      (let [{:keys [backing state-atom]} (fresh)
            st (urd-store-on backing)]
        (<!! (store/write! st {:writes {:n 0} :durable? true}))
        (<!! (store/write! st {:writes {:n 1} :durable? true}))
        (store/write! st {:writes {:n 2} :durable? true})
        (crash/simulate-crash! state-atom)
        (let [restored (<!! (store/restore (urd-store-on backing)))
              got (writes-in restored)]
          (is (contains? #{[{:n 0} {:n 1}] [{:n 0} {:n 1} {:n 2}]} got)
              (str "must be a prefix of what was written, whole records only: "
                   (pr-str got))))))))

;; ============================================================
;; Compaction
;; ============================================================

(deftest a-checkpoint-replaces-the-log-and-survives-a-reopen
  (testing "`fold` bounds the HEAP; `checkpoint!` bounds the LOG

           Without it a node that has been up for a week restarts by replaying
           a week, because the write log IS the history. The algorithm supplies
           a short list of records that folds to the same state, so `fold`'s
           contract is untouched and no algorithm that has not opted in changes.

           The reopen is the half that matters: compaction cannot rewrite
           konserve's append log in place -- it is a chain of separate store
           keys -- so a checkpoint writes a fresh log and flips one pointer. A
           store that came back reading the DEFAULT key after a checkpoint
           would silently restore from an empty log, which is data loss dressed
           as a fast restart."
    (let [{:keys [backing]} (fresh)
          st (urd-store-on backing)]
      (doseq [i (range 20)]
        (is (true? (<!! (store/write! st {:writes {:n i} :durable? true})))))
      (is (= 20 (count (writes-in (<!! (store/restore st))))))

      ;; One record summarising twenty.
      (is (true? (<!! (store/checkpoint! st [{:writes {:n 19} :durable? true}]))))
      (is (= [{:n 19}] (writes-in (<!! (store/restore st))))
          "the log is now the summary and nothing else")

      ;; Writes after a checkpoint land in the NEW log, not the old one.
      (<!! (store/write! st {:writes {:n 20} :durable? true}))
      (is (= [{:n 19} {:n 20}] (writes-in (<!! (store/restore st))))
          "and the writer follows the pointer -- an append that kept writing to
           the old key would land in a log nothing reads")

      ;; A fresh process on the same backing.
      (let [reopened (<!! (store/restore (urd-store-on backing)))]
        (is (= [{:n 19} {:n 20}] (writes-in reopened))
            "a reopened store finds the COMPACTED log, not the default key")
        (is (= {:n 20} (:durable reopened)))))))

(deftest a-crash-during-a-checkpoint-leaves-one-log-or-the-other
  (testing "a crashed checkpoint never loses the log it was replacing

           What this DOES establish: crashing at any of the six write-path
           points while building the new log leaves the old one intact and
           readable, so a checkpoint can fail without costing anything.

           What it does NOT establish, and I would rather say so than imply
           otherwise: the ORDERING inside `checkpoint!` -- new log written in
           full, then the pointer flipped, then the old log swept. I mutated
           that order to sweep first, which should be able to lose everything,
           and this test still passed. The reason is that konserve's crash
           points target a position within ONE write's path, so the injected
           crash always lands on the first append of the new log and the
           checkpoint aborts long before it reaches the flip. Demonstrating the
           ordering needs a fault injected between two whole operations, which
           this harness cannot express.

           So the ordering is argued rather than tested, and the argument is in
           `checkpoint!`'s comments. Treat it accordingly."
    (doseq [point [:after-write-header :after-write-meta :after-write-value
                   :after-sync :after-atomic-move :after-sync-store]]
      (let [{:keys [backing crash-point-atom state-atom]} (fresh)
            st (urd-store-on backing)]
        (doseq [i (range 5)]
          (<!! (store/write! st {:writes {:n i} :durable? true})))

        (crash/set-crash-point! crash-point-atom point)
        (<!! (store/checkpoint! st [{:writes {:n 99} :durable? true}]))
        (crash/simulate-crash! state-atom)
        (crash/clear-crash-point! crash-point-atom)

        (let [restored (<!! (store/restore (urd-store-on backing)))
              got (writes-in restored)]
          (is (not (instance? Throwable restored))
              (str point ": the store must reopen after a crashed checkpoint"))
          ;; `[]` is NOT in this set, and leaving it in was the whole problem
          ;; with the first version of this test: an empty result is exactly
          ;; what sweeping the old log BEFORE the pointer flip produces, so
          ;; permitting it let the test pass with the ordering inverted. The
          ;; old log exists until the flip; there is no legal moment at which a
          ;; reopened store sees neither log.
          (is (contains? #{(mapv (fn [i] {:n i}) (range 5))   ; old log intact
                           [{:n 99}]}                         ; new log adopted
                         got)
              (str point ": one log or the other, never neither -- got "
                   (pr-str got))))))))
