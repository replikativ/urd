(ns urd.consensus.apphash
  "The convention by which a decided value commits to APPLICATION state.

  ## What is missing without it

  Nothing in urd's consensus state says anything about the application's state.
  Consensus agrees on an ORDER of values; whether two nodes that applied the
  same order ended up in the same state is not something any node can check. A
  validator whose application diverged -- a non-deterministic transaction, a
  storage bug, a different library version -- keeps voting, and every vote it
  casts is on behalf of a state nobody else has. It is a silent, permanent
  fork of exactly the thing consensus exists to keep identical.

  The fix costs no protocol change, because values are OPAQUE to urd: the
  value carries a digest of the application state, and the quorum that decides
  the value certifies the digest along with it.

  ## LAGGING by one, and why that is the right choice rather than a compromise

  The digest describes the state as of the LAST DECIDED value, not as of the
  value carrying it. Value N says `here is what my application looked like
  after N-1`.

  The alternative -- the digest of the state after applying THIS value -- reads
  as more direct and costs much more. The proposer would have to execute its
  own proposal speculatively before proposing, and every validator would have
  to execute it speculatively before VOTING, because the digest cannot be
  checked without doing so. That makes execution part of the voting path,
  which means it must be deterministic, bounded, and fast enough to fit inside
  a vote timeout, on every validator, for every proposal -- including proposals
  that never get decided.

  Lagging by one removes all of it. A validator checking value N compares the
  digest against a state it computed long ago, when N-1 was decided. It is a
  map lookup, not an execution. CometBFT made this choice for these reasons and
  its `AppHash` has this meaning.

  What it costs is one block of latency in DETECTION: divergence caused by
  value N is caught when N+1 is proposed. That is still before anything is
  built on N, because N+1 is where the chain would continue -- so the fork is
  refused rather than discovered later.

  ## Opaque, and it must stay opaque

  urd never computes a digest, never inspects one, and has no opinion about how
  it is derived. datahike supplies one for free with `:crypto-hash? true`,
  where the commit-id IS a merkle hash over the stored roots -- but that is one
  implementation of the convention, not the convention. A plain hash of an
  application's own state is another, and so is anything Proximum or Scriptum
  produce. Everything here is `=` on values the application chose.

  ## An ABSENT digest is not a valid one

  The tempting reading of a missing `:app-hash` is `this value makes no claim,
  so there is nothing to check`. That is a bypass: an attacker proposing a
  value simply omits the field and the check never runs. Every proposal it
  makes is then exempt from exactly the guard that would catch it.

  So `checker` refuses a value with no digest unless `:require?` is explicitly
  set to false. This follows `urd.consensus.auth/authenticator`, and for the
  same reason -- a permissive default is how a check that is described but not
  performed survives review.")

(def digest-key
  "Where the digest rides on the value.

  A namespaced keyword would be tidier and is deliberately not used: values
  cross the wire as EDN and are written to application-defined stores, and a
  namespaced key is one more thing an integrator has to get exactly right for a
  check to run at all. A check that silently does not run is the failure mode
  this namespace exists to prevent."
  :app-hash)

(defn attach
  "Put `digest` on `value`, to be certified by whatever quorum decides it.

  Called by the application in `on-propose`, with the digest of its state as of
  the last value it applied. `nil` attaches nothing, so an application that
  cannot compute a digest yet -- at genesis, before anything is applied --
  produces a value that says so rather than one claiming an empty state."
  [value digest]
  (if (some? digest)
    (assoc value digest-key digest)
    value))

(defn claimed
  "The digest `value` claims, or nil if it makes no claim."
  [value]
  (get value digest-key))

(defn agrees?
  "Does `value`'s claim match `current`?

  `nil` `current` means the application has applied nothing yet and has no
  state to compare -- the genesis case -- and any claim is accepted, because
  refusing here would prevent the first value from ever being decided."
  [value current]
  (or (nil? current)
      (= (claimed value) current)))

(defn checker
  "Build a `:valid-fn` that refuses a value whose digest disagrees with ours.

  `current-fn` is a 0-arg function returning this node's digest for the state
  it has applied so far -- read at call time, not captured, because it changes
  as values are applied.

  `:require?` defaults to TRUE: a value carrying no digest is refused. See the
  namespace docstring; the permissive reading is a bypass. Pass `false` only
  for a deployment where some proposers do not yet attach one, and understand
  that it exempts exactly the values an attacker controls.

  Returns a predicate suitable wherever an algorithm takes `:valid-fn`."
  ([current-fn] (checker current-fn {}))
  ([current-fn {:keys [require?] :or {require? true}}]
   (fn [value]
     (let [current (current-fn)]
       (cond
         ;; Nothing applied yet: no state to disagree with.
         (nil? current) true
         (nil? (claimed value)) (not require?)
         :else (= (claimed value) current))))))

(defn verify!
  "Check a DECIDED value against our own state, and call `on-mismatch` if it
  disagrees.

  Separate from `checker` because the two answer different questions at
  different times. `checker` runs before voting and its answer is `do not vote
  for this`; a proposal that fails it is simply not adopted, and the network
  continues without us. This runs when a value has ALREADY been decided by a
  quorum, and a mismatch here means the quorum's application state is not ours
  -- we are the ones who diverged.

  That is not recoverable by voting differently and it must not be silent. The
  application decides what to do (halt, alarm, resync), which is why this takes
  a callback rather than throwing: for a ledger, continuing to apply
  transactions onto a state the network disagrees with makes the divergence
  deeper with every one."
  [value current on-mismatch]
  (if (agrees? value current)
    true
    (do (when on-mismatch
          (on-mismatch {:claimed (claimed value) :ours current :value value}))
        false)))
