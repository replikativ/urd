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

  Ported from `avalanchego/snow/consensus/snowball` (Aug 2026). Two notes on
  drift from the papers, both verified against that tree:

  - `betaVirtuous` / `betaRogue` are GONE. They were replaced by a single
    `beta` plus a list of (alpha-confidence, beta) termination conditions.
    Production always uses exactly one pair; the multi-condition path (\"early
    termination\": a stronger quorum finalizes in fewer rounds) is exercised
    only by tests. We model the list, since it costs nothing and the
    single-condition case is just a list of one.

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

(defn valid-params?
  "Are these parameters self-consistent?

  A total predicate; the natural first thing to machine-check."
  [{:keys [k alpha-preference alpha-confidence beta]}]
  (boolean
   (and k alpha-preference alpha-confidence beta
        (pos? k)
        (pos? beta)
        (< (/ k 2) alpha-preference)
        (<= alpha-preference alpha-confidence)
        (<= alpha-confidence k))))

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
   :confidence [0]
   :finalized? false})

(defn- termination-conditions [params]
  [{:alpha-confidence (:alpha-confidence params) :beta (:beta params)}])

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
        (loop [i 0, sf sf]
          (if (>= i (clojure.core/count tcs))
            sf
            (let [{:keys [alpha-confidence beta]} (nth tcs i)]
              (if (< votes alpha-confidence)
                ;; Clear this counter and every stricter one, then stop.
                (assoc sf :confidence
                       (vec (map-indexed (fn [j c] (if (>= j i) 0 c)) (:confidence sf))))
                (let [c' (inc (nth (:confidence sf) i))
                      sf (assoc-in sf [:confidence i] c')]
                  (if (>= c' beta)
                    (assoc sf :finalized? true)
                    (recur (inc i) sf)))))))))))

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
