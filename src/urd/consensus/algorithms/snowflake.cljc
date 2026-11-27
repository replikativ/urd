(ns urd.consensus.algorithms.snowflake
  "Snowflake and Snowball: the repeated-sampling core of the Avalanche family.

  These are pure functions over a small map. They are separated from the
  Snowman node deliberately -- they are total, they have real invariants, and
  they are the natural first target for machine-checked verification.

  ## The family

  Slush keeps only a preference. Snowflake adds a CONSECUTIVE-success
  confidence counter and an absorbing `finalized` flag. Snowball adds a
  CUMULATIVE preference-strength tally and returns the argmax of that instead of
  the last successful poll's choice. Each is a strict superset of the previous.

  Ported from `avalanchego/snow/consensus/snowball` (Aug 2026).

  ## Which of these avalanchego actually deploys

  **Snowflake.** Not Snowball. `chains/manager.go:933` and `:1358` both build
  `&smcon.Topological{Factory: snowball.SnowflakeFactory}`, and
  `git log -S SnowflakeFactory -- chains/manager.go` returns exactly one commit:
  `db3b57a96f` -- make snowman use snowflake directly instead of snowball
  (#3403). `SnowballFactory` is exported, exercised by the package's own tests,
  and wired into no chain.

  So Snowball below -- the cumulative `:strength` tally, the argmax preference,
  the finalized-versus-argmax asymmetry that `accept-weird-color` pins -- is
  reference material rather than production behaviour. It is kept because it is
  the published algorithm, because the papers are stated in its terms, and
  because a library covering the family should be able to express it. It is not
  kept under the impression that it is what the network runs.

  Two further notes on drift from the papers, both verified against that tree:

  - `betaVirtuous` / `betaRogue` are GONE. They were replaced by a single
    `beta` plus a list of (alpha-confidence, beta) termination conditions.
    Production always uses exactly one pair; the multi-condition path (\"early
    termination\": a stronger quorum finalizes in fewer rounds) is exercised
    only by tests. We model the list, since it costs nothing and the
    single-condition case is just a list of one. `termination-conditions` is
    public and overridable so the multi-condition path can actually be
    CONSTRUCTED: while the pairs were derived from `params` inside a private
    function, no caller could build an instance with more than one counter, the
    partial-clear semantics that are the vector's whole reason for existing were
    unobservable, and the claim above was not true of the code.

  - The Avalanche DAG protocol has been DELETED from avalanchego entirely
    (the X-Chain moved to Snowman in Cortina). Only Snowman remains, so the
    papers are the sole source for the DAG variant.

  ## Parameters

      k                sample size per poll
      alpha-preference votes needed to move the preference
      alpha-confidence votes needed to increment confidence
      beta             consecutive successes needed to finalize

  Validity (`parameters.go:93-116`):

      k/2 < alpha-preference <= alpha-confidence <= k

  The first conjunct forces a strict majority of the sample, so two conflicting
  choices cannot both clear `alpha-preference` in one poll of one honest node.
  The second guarantees that any poll which increments confidence also moved the
  preference -- which is what makes the beta-run characterisation below hold."
  (:refer-clojure :exclude [count]))

;; ============================================================
;; Parameters
;; ============================================================

(defn termination-conditions
  "The (alpha-confidence, beta) pairs this instance finalizes on.

  `:termination-conditions` supplied explicitly wins; otherwise the single
  condition built from `:alpha-confidence`/`:beta`, which is
  `newSingleTerminationCondition` (`parameters.go:131-138`) and is what
  avalanchego actually deploys.

  This is public and overridable so the multi-condition path is REACHABLE.
  It was not: the pairs were derived from `params` inside a private function,
  so no caller could construct an instance with more than one counter, and the
  partial-clear semantics of the confidence vector -- the only reason the vector
  is a vector -- could never be observed. `snowflake_test.go:10-23` drives every
  one of its four generators off a three-element table."
  [params]
  (or (seq (:termination-conditions params))
      [{:alpha-confidence (:alpha-confidence params) :beta (:beta params)}]))

(defn valid-params?
  "Are these parameters self-consistent?

  A total predicate; the natural first thing to machine-check."
  [{:keys [k alpha-preference alpha-confidence beta] :as params}]
  (boolean
   (and k alpha-preference alpha-confidence beta
        (pos? k)
        (pos? beta)
        (< (/ k 2) alpha-preference)
        (<= alpha-preference alpha-confidence)
        (<= alpha-confidence k)
        ;; Every explicit termination condition must be individually valid:
        ;; a condition whose alpha-confidence sits below alpha-preference would
        ;; increment confidence on a poll that did not move the preference,
        ;; breaking the beta-run characterisation for every counter after it.
        (every? (fn [{ac :alpha-confidence b :beta}]
                  (and (integer? ac) (integer? b) (pos? b)
                       (<= alpha-preference ac) (<= ac k)))
                (termination-conditions params)))))

(def default-params
  ;; avalanchego's production defaults (parameters.go:38-47), scaled down: the
  ;; real network uses k=20/alpha=15/beta=20, which is impractical in a
  ;; simulation of five nodes.
  {:k 5 :alpha-preference 3 :alpha-confidence 3 :beta 3})

;; ============================================================
;; Snowflake
;; ============================================================

(defn snowflake
  "A fresh Snowflake instance preferring `choice`."
  [params choice]
  {:params params
   :preference choice
   ;; One counter per termination condition. Production has exactly one.
   :confidence (vec (repeat (clojure.core/count (termination-conditions params)) 0))
   :finalized? false})

(defn- run-termination
  "Update each condition's counter in the caller's configured order."
  [sf votes]
  (reduce (fn [st [i {:keys [alpha-confidence beta]}]]
            (let [c (if (>= votes alpha-confidence) (inc (get-in st [:confidence i])) 0)
                  st (assoc-in st [:confidence i] c)]
              (if (>= c beta) (reduced (assoc st :finalized? true)) st)))
          sf
          (map-indexed vector (termination-conditions (:params sf)))))

(defn snowflake-record-poll
  "Apply a poll result: `votes` for `choice` out of k.

  Total. Mirrors `nnary_snowflake.go:54-88` exactly:

    - finalized is ABSORBING -- a finalized instance ignores everything;
    - below alpha-preference is indistinguishable from an unsuccessful poll;
    - a preference FLIP zeroes confidence first, which is why preference churn
      can never accumulate toward finalization;
    - confidence increments by at most one per poll."
  [sf votes choice]
  (let [{:keys [params]} sf
        tcs (termination-conditions params)]
    (cond
      (:finalized? sf) sf

      (< votes (:alpha-preference params))
      (assoc sf :confidence (vec (repeat (clojure.core/count tcs) 0)))

      :else
      (let [flipped? (not= choice (:preference sf))
            sf (cond-> sf flipped? (assoc :confidence (vec (repeat (clojure.core/count tcs) 0))))
            sf (assoc sf :preference choice)]
        (run-termination sf votes)))))

(defn snowflake-record-unsuccessful-poll
  "A poll that failed to reach alpha-preference. Clears confidence; `finalized?`
  is untouched, since it is absorbing."
  [sf]
  (assoc sf :confidence (vec (repeat (clojure.core/count (:confidence sf)) 0))))

;; ============================================================
;; Snowball
;; ============================================================

(defn snowball
  "A fresh Snowball instance preferring `choice`."
  [params choice]
  {:snowflake (snowflake params choice)
   :preference choice
   :strength {}})

(defn snowball-record-poll
  "Apply a poll result.

  Snowball's only delta from Snowflake is the preference rule: it tracks a
  CUMULATIVE tally per choice and prefers the argmax, where Snowflake prefers
  whatever won the last successful poll. Flips only on STRICT improvement, so
  ties are broken lazily in favour of the incumbent (`nnary_snowball.go:50-61`)."
  [sb votes choice]
  (let [params (get-in sb [:snowflake :params])
        sb (if (>= votes (:alpha-preference params))
             (let [strength (update (:strength sb) choice (fnil inc 0))
                   best (get strength (:preference sb) 0)]
               (assoc sb
                      :strength strength
                      :preference (if (> (get strength choice 0) best)
                                    choice
                                    (:preference sb))))
             sb)]
    (update sb :snowflake snowflake-record-poll votes choice)))

(defn snowball-preference
  "The current preference.

  Note the asymmetry, which is NOT cosmetic: once finalized, Snowball returns
  the SNOWFLAKE's preference, not its own argmax. The two can disagree at the
  instant of finalization, and the snowflake's choice wins. avalanchego pins
  this with `TestBinarySnowballAcceptWeirdColor`; reproduce it or diverge."
  [sb]
  (if (get-in sb [:snowflake :finalized?])
    (get-in sb [:snowflake :preference])
    (:preference sb)))

(defn finalized? [sb] (get-in sb [:snowflake :finalized?]))

(defn confidence [sb] (get-in sb [:snowflake :confidence]))

;; ============================================================
;; Unary and binary instances
;;
;; The n-ary form above decides among several choices at once. The Tree in
;; `snowtree` instead decides the BITS of the winning id, one node at a time,
;; and needs two narrower instances for that: a unary one for a run of bits
;; where nothing conflicts, and a binary one for the bit where two branches
;; diverge. `unary_snowflake.go` and `binary_snowflake.go`.
;;
;; Both are Snowflake, not Snowball -- there is no unary or binary Snowball in
;; the Tree's path, and `SnowflakeFactory` is what a running node passes in
;; anyway. See the note at the top of this namespace.
;; ============================================================

(defn unary-snowflake
  "A unary instance: no choice at all, only confidence that the bits it covers
  are settled."
  [params]
  {:params params
   :confidence (vec (repeat (clojure.core/count (termination-conditions params)) 0))
   :finalized? false})

(defn unary-record-poll
  "`unary_snowflake.go:45-64`.

  Note what is NOT here: no `finalized?` guard, and no alpha-preference check.
  Both live in the caller -- `unaryNode.RecordPoll` tests alpha before calling
  -- so this is asymmetric with `binary-record-poll`, which has both. The
  asymmetry is avalanchego's and is reproduced rather than tidied, because
  tidying it would silently move where an alpha threshold is enforced."
  [sf votes]
  (run-termination sf votes))

(defn unary-record-unsuccessful-poll [sf]
  (assoc sf :confidence (vec (repeat (clojure.core/count (:confidence sf)) 0))))

(defn unary-extend
  "`Extend(bit)`: become a binary instance preferring `bit`.

  The accumulated confidence CARRIES OVER. That is the point of the Tree: a run
  of bits that has been polled into agreement does not start again from zero
  when a new choice forces the run to split."
  [sf bit]
  {:params (:params sf)
   :preference bit
   :confidence (:confidence sf)
   :finalized? (:finalized? sf)})

(defn binary-snowflake
  "A binary instance: which of two branches, 0 or 1, at one bit."
  [params bit]
  {:params params
   :preference bit
   :confidence (vec (repeat (clojure.core/count (termination-conditions params)) 0))
   :finalized? false})

(defn binary-record-poll
  "`binary_snowflake.go:47-80`. `bit` is 0 or 1.

  Unlike the unary form this DOES guard `finalized?` and DOES check
  alpha-preference itself, and a flip clears confidence before the run --
  the same consecutive-poll rule as the n-ary instance, over two choices."
  [sf votes bit]
  (cond
    (:finalized? sf) sf

    (< votes (:alpha-preference (:params sf)))
    (unary-record-unsuccessful-poll sf)

    :else
    (-> sf
        (cond-> (not= bit (:preference sf))
          (assoc :confidence (vec (repeat (clojure.core/count (:confidence sf)) 0))))
        (assoc :preference bit)
        (run-termination votes))))

(defn binary-record-unsuccessful-poll [sf]
  (unary-record-unsuccessful-poll sf))

(defn instance-finalized?
  "Works for a unary or a binary instance -- both keep the flag at the top."
  [sf]
  (:finalized? sf))
