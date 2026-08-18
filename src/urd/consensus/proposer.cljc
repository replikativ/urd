(ns urd.consensus.proposer
  "Weighted round-robin proposer selection.

  Ported from CometBFT (`types/validator_set.go:131-250`, read Aug 2026) and
  `spec/consensus/proposer-selection.md`. Kept OUT of the consensus state
  machine on purpose: it is a total function of (priorities, powers, round), so
  it can be tested and reasoned about without a node, and an algorithm that
  wants a different eligibility rule can swap it.

  ## The algorithm

  Per selection run:

    1. **scale** -- if `max - min > 2 * totalPower`, divide every priority by
       `ceil(diff / 2*totalPower)`, bounding the priority window;
    2. **center** -- subtract the mean, so priorities stay near zero and cannot
       drift;
    3. repeat `times` times: **increment** every validator by its voting power,
       **elect** the argmax, then **demote** the winner by the total power.

  Note the implementation does scale+center ONCE, before the loop, while the
  spec document's pseudocode does it per run. We follow the implementation,
  because it is what actually produced every chain's history; the difference
  shows up only when `times > 1`, i.e. when skipping rounds.

  ## Two portability hazards, both real

  **`center` must floor-divide, not truncate.** CometBFT computes the average
  with `big.Int.Div`, which is Euclidean (rounds toward -infinity), NOT `Quo`
  (which truncates toward zero). Clojure's `quot` truncates, so using it here
  would diverge from CometBFT exactly when the priority sum is negative --
  which is the normal case, since the winner is demoted by the total power
  every round. `rescale` on the other hand uses Go's `/` on int64, which DOES
  truncate toward zero, so `quot` is correct there. Two divisions, two
  different roundings, ten lines apart.

  **Ties are broken by validator id, ascending.** CometBFT compares raw address
  bytes (`types/validator.go:76`). We compare ids with `clojure.core/compare`,
  which requires the ids to be mutually comparable -- keywords, strings or
  numbers, not a mixture.")

(defn- floor-div
  "Euclidean division, matching Go's `big.Int.Div`.

  `(quot -1 4)` is 0 but `(floor-div -1 4)` is -1. See the namespace docstring."
  [a b]
  (quot (- a (mod a b)) b))

(defn total-power [powers]
  (reduce + 0 (vals powers)))

(defn rescale
  "Bound the priority window to `diff-max`.

  `ratio = ceil(diff / diff-max)`, applied only when the window is actually too
  wide. Truncating division here is deliberate -- Go's int64 `/`."
  [priorities diff-max]
  (if (or (empty? priorities) (<= diff-max 0))
    priorities
    (let [vs (vals priorities)
          diff (- (apply max vs) (apply min vs))]
      (if (> diff diff-max)
        (let [ratio (quot (+ diff diff-max -1) diff-max)]
          (into {} (map (fn [[k v]] [k (quot v ratio)])) priorities))
        priorities))))

(defn center
  "Subtract the mean priority, so the priorities cannot drift away from zero."
  [priorities]
  (if (empty? priorities)
    priorities
    (let [avg (floor-div (reduce + 0 (vals priorities)) (count priorities))]
      (into {} (map (fn [[k v]] [k (- v avg)])) priorities))))

(defn- elect-one
  "Highest priority wins; ties go to the lower id. Deterministic by
  construction -- `order` is supplied sorted, so map iteration order cannot
  leak in."
  [priorities order]
  (reduce (fn [best id]
            (cond
              (nil? best) id
              (> (priorities id) (priorities best)) id
              :else best))
          nil
          order))

(defn- increment-once
  "One round of the selection loop. Returns [priorities' winner]."
  [priorities powers total order]
  (let [bumped (into {} (map (fn [[k v]] [k (+ v (get powers k 0))])) priorities)
        winner (elect-one bumped order)]
    [(update bumped winner - total) winner]))

(defn elect
  "Run the selection `times` times. Returns {:proposer id :priorities p'}.

  `times` must be positive; CometBFT panics otherwise and there is no sensible
  answer for zero (nobody has been elected yet)."
  [priorities powers times]
  (when-not (pos? times)
    (throw (ex-info "elect needs a positive `times`" {:times times})))
  (when (empty? priorities)
    (throw (ex-info "elect needs a non-empty priority map" {})))
  (let [total (total-power powers)
        order (vec (sort (keys priorities)))
        start (-> priorities (rescale (* 2 total)) center)]
    (loop [p start, i 0, winner nil]
      (if (>= i times)
        {:proposer winner :priorities p}
        (let [[p' w] (increment-once p powers total order)]
          (recur p' (inc i) w))))))

(defn proposer-for
  "Who proposes at `round` of the height whose base priorities are `priorities`?

  Rounds are 0-based, so round r takes r+1 increments. This is a pure query: it
  does not advance the stored priorities, matching CometBFT's
  `CopyIncrementProposerPriority`."
  [priorities powers round]
  (:proposer (elect priorities powers (inc round))))

(defn advance
  "The base priorities for the next height: one increment, permanently applied."
  [priorities powers]
  (:priorities (elect priorities powers 1)))

(defn initial-priorities
  "Everyone starts at zero, as at genesis."
  [validators]
  (into {} (map (fn [v] [v 0])) validators))

(defn new-validator-priority
  "The priority a validator joining a set of `total` voting power is given.

  `-(P + P>>3)`, documented as -1.125*P (`validator_set.go:543-550`), to stop a
  freshly added validator from proposing immediately. Note the shift is an
  INTEGER shift, so for P < 8 the 0.125 penalty truncates to zero and the
  priority is exactly -P -- the intended extra margin vanishes entirely on
  small-power sets. Kept here (validator-set changes are otherwise out of
  scope) because it is the one place the reference implementation's arithmetic
  silently does something other than what its comment says."
  [total]
  (- (+ total (bit-shift-right total 3))))
