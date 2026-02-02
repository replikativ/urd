# Urd

[![CircleCI](https://circleci.com/gh/replikativ/urd.svg?style=shield)](https://circleci.com/gh/replikativ/urd)
[![Clojars](https://img.shields.io/clojars/v/org.replikativ/urd.svg)](https://clojars.org/org.replikativ/urd)
[![Slack](https://img.shields.io/badge/slack-join_chat-brightgreen.svg)](https://clojurians.slack.com/archives/CB7GJAN0L)

> *In Norse mythology, [Urðr](https://en.wikipedia.org/wiki/Urðr) (Old Norse: "fate") is one of the three Norns who carve runes into Yggdrasil, establishing immutable truth.*

**Urd** - Byzantine Fault Tolerant consensus for distributed copy-on-write systems.

A pure functional consensus framework designed to coordinate finalization across heterogeneous storage systems (Datahike, Git, ZFS, IPFS, etc.) using [Yggdrasil](https://github.com/replikativ/yggdrasil) snapshot protocols.

## Why Urd?

**Yggdrasil** provides causal consistency through copy-on-write snapshots and HLC timestamps - perfect for trusted environments.

**Urd** adds Byzantine Fault Tolerant consensus - enabling coordination in adversarial or permissionless environments where validators may be malicious.

**Key Insight:** Consensus metadata (signatures, votes, certificates) lives in a separate consensus log, not in native storage. Each system writes snapshots once (immutable), while Urd coordinates finalization separately.

```
┌────────────────────────────────────┐
│  Native Storage (Immutable)        │
│  Datahike: snap-1 → {:eavt ...}    │
│  Git:      abc123 → tree object    │
│  ZFS:      pool/snap@1 → dataset   │
│  (NO CONSENSUS METADATA)           │
└────────────────────────────────────┘
              ↓
    (referenced by snapshot-id)
              ↓
┌────────────────────────────────────┐
│  Urd Consensus Log (Urðarbrunnr)   │
│  proposal-id → {:snapshots {...}   │
│                 :votes {...}       │
│                 :finalized? true   │
│                 :height 1234}      │
│  (ALL CONSENSUS METADATA)          │
└────────────────────────────────────┘
```

## Features

### ✅ Pure Functional State Machine

Consensus algorithms as pure functions with explicit effects:

```clojure
(defprotocol ConsensusAlgorithm
  (initial-state [this config])
  (handle-event [this state event]))
  ;; Returns: {:state new-state :effects [effect...]}
```

**Benefits:**
- Testable without async/mocking
- REPL-friendly development
- Effect interpretation separates pure logic from I/O
- Easy to reason about state transitions

### ✅ Pluggable Algorithms

Framework supports multiple consensus algorithms:

- **Round-Robin** (reference implementation) - Simple deterministic proposer selection
- **CometBFT-style** (planned) - Multi-phase BFT with prevote/precommit, locking mechanism
- **Raft** (planned) - Leader election + log replication (CFT)
- **Avalanche** (planned) - Leaderless probabilistic consensus via sampling
- **Narwhal-Bullshark** (planned) - DAG-based with separated mempool

Current focus: Generalized state machine framework that can express all algorithms.

### ✅ Network-Agnostic Runtime

Runtime interprets effects and manages async operations:

```clojure
;; Effects are data
[:broadcast {:topic :proposals :message proposal}]
[:set-timer {:timer-id :timeout-1 :duration 3000 :timeout-event {...}}]
[:persist {:persist-type :hard-state :data {...}}]
[:finalize {:data committed-proposal}]

;; Runtime interprets them
(defn interpret-effect [runtime effect] ...)
```

**Supports:**
- Mock network (for testing)
- Kabel P2P (WebSocket-based)
- Any transport implementing `ConsensusNetwork` protocol

### ✅ Cryptographic Signatures

ED25519 signing for Byzantine fault tolerance:

```clojure
(require '[urd.crypto :as crypto])

(def keypair (crypto/ed25519-keypair))
(def signed (crypto/sign-snapshot snapshot (:private keypair) (:public keypair)))
(crypto/verify-signature signed)  ; => true
```

- **32-byte keys, 64-byte signatures**
- ~70k signatures/sec, ~24k verifications/sec
- Deterministic (same message + key = same signature)

### ✅ Multi-Validator Certificates

Accumulate signatures for 2f+1 quorum:

```clojure
;; 4 validators (quorum = 3)
(def certificate (-> v1-signed
                    (crypto/add-signature v2-id v2-sig)
                    (crypto/add-signature v3-id v3-sig)))

(crypto/has-quorum? certificate validator-set)  ; => true
(crypto/verify-certificate certificate validator-set)
```

### ✅ Consensus Log (Urðarbrunnr)

"Urd's Well" - where the gods hold council beneath Yggdrasil:

```clojure
(require '[urd.log :as log])

(def consensus-log (log/create-consensus-log store validator-set))

;; Propose signed snapshot
(def proposal-id (<!! (log/propose! consensus-log signed-snapshot {})))

;; Accumulate votes
(<!! (log/add-vote! consensus-log proposal-id validator-2-id sig-2))
(<!! (log/add-vote! consensus-log proposal-id validator-3-id sig-3))

;; Check quorum
(<!! (log/has-quorum? consensus-log proposal-id validator-set))  ; => true

;; Finalize at height
(<!! (log/finalize! consensus-log proposal-id 1))
```

**Proposal State Machine:**
```
:proposed → :voting → :certified → :finalized
                 ↓
              :rejected
```

## Installation

Add to your `deps.edn`:

```clojure
{:deps {org.replikativ/yggdrasil {:mvn/version "0.1.7"}
        org.replikativ/urd {:mvn/version "0.1.0"}}}
```

## Quick Start

### 1. Set Up Validators

```clojure
(require '[urd.crypto :as crypto]
         '[urd.consensus.runtime :as runtime]
         '[urd.consensus.algorithms.round-robin :as rr]
         '[urd.consensus.network :as net]
         '[urd.log :as log]
         '[konserve.memory :refer [new-mem-store]]
         '[clojure.core.async :refer [<!!]])

;; Create validator keypairs
(def v1-kp (crypto/ed25519-keypair))
(def v2-kp (crypto/ed25519-keypair))
(def v3-kp (crypto/ed25519-keypair))

(def validator-set {(java.util.UUID/randomUUID) (:public v1-kp)
                    (java.util.UUID/randomUUID) (:public v2-kp)
                    (java.util.UUID/randomUUID) (:public v3-kp)})
```

### 2. Start Consensus Runtime

```clojure
;; Each validator runs a runtime
(def store (<!! (new-mem-store)))
(def consensus-log (log/create-consensus-log store validator-set))
(def state-machine (rr/create validator-set))
(def network (net/create-mock-cluster [validator-ids]))

(def rt (<!! (runtime/start-runtime!
               {:peer-id my-validator-id
                :state-machine state-machine
                :network network
                :consensus-log consensus-log
                :on-propose (fn [] my-proposal)
                :on-finalize (fn [proposal height]
                              (println "Finalized at height" height))})))
```

### 3. Trigger Consensus

```clojure
;; Start consensus round
(runtime/send-event! rt {:type :start-round})

;; Wait for finalization
(<!! (timeout 3000))

;; Query finalized proposals
(<!! (log/get-finalized-at-height consensus-log 0))
```

## Architecture

### State Machine Layer

Pure functional consensus algorithms:

```clojure
(defrecord RoundRobin [validator-set]
  ConsensusAlgorithm
  (initial-state [this config] ...)
  (handle-event [this state event]
    ;; Pure function: state + event → {:state ... :effects [...]}
    (case (:type event)
      :start-round (enter-proposing-phase state)
      :proposal-received (handle-proposal state event)
      :vote-received (handle-vote state event)
      :quorum-reached (finalize-and-advance state event))))
```

**Events:**
- `:start-round` - Begin new consensus round
- `:proposal-ready` - Application provides proposal
- `:proposal-received` - Proposal from network
- `:vote-received` - Vote from peer
- `:quorum-reached` - Threshold met
- `:timeout` - Timer expired

**Effects:**
- `[:broadcast {...}]` - Send to all peers
- `[:set-timer {...}]` - Schedule timeout
- `[:persist {...}]` - Store to disk
- `[:finalize {...}]` - Commit proposal
- `[:request-proposal {...}]` - Ask application for data

### Runtime Layer

Interprets effects and manages async operations:

```clojure
(defn start-runtime! [config]
  ;; Creates:
  ;; - Event loop (core.async go-loop)
  ;; - Timer management
  ;; - Network subscriptions
  ;; - Effect interpreter
  (go-loop [state (sm/initial-state ...)]
    (let [event (<! event-chan)
          {:keys [state effects]} (sm/handle-event state-machine state event)]
      (doseq [effect effects]
        (interpret-effect runtime effect))
      (recur state))))
```

### Network Layer

Pluggable transport:

```clojure
(defprotocol ConsensusNetwork
  (broadcast! [this topic message])
  (subscribe! [this topic handler])
  (unsubscribe! [this topic handle])
  (get-peer-count [this])
  (close-network! [this]))
```

**Implementations:**
- **Mock cluster** - In-memory channels for testing
- **Kabel P2P** - WebSocket-based real network (production-ready)

## Testing

Comprehensive test suite with 72 tests, 237 assertions:

```bash
# Run all tests
clj -M:test

# Run specific test namespace
clj -M:test -n urd.consensus.runtime-test

# Run with generative testing
clj -M:test -n urd.consensus.algorithms.round-robin-generative-test
```

**Test coverage:**
- ✅ Crypto operations (ED25519 sign/verify)
- ✅ Consensus log (propose, vote, finalize)
- ✅ Round-robin algorithm (all state transitions)
- ✅ Runtime integration (event loop, timers, network)
- ✅ Kabel P2P network (broadcast, subscribe, multiple peers)
- ✅ Generative testing (random event sequences)
- ✅ Fault injection (network delays, dropped messages)

## Development Status

**Current: Phase 1 - Foundation Complete ✅**

- [x] Pure functional state machine framework
- [x] Round-robin consensus algorithm
- [x] Event/effect abstraction
- [x] Runtime with event loop
- [x] Mock network for testing
- [x] Kabel P2P integration
- [x] ED25519 signatures
- [x] Consensus log (propose/vote/finalize)
- [x] Full test coverage

**Next: Phase 2 - Generalized Framework** 🚧

Goal: State machine abstraction that can express CometBFT, Raft, Avalanche, and Narwhal-Bullshark.

- [ ] Parameterized event types (`:vote-type`, `:quorum-type`, `:timeout-type`)
- [ ] Algorithm-specific state extensions (`:algorithm-state`)
- [ ] Rich effect vocabulary (`:sample-peers`, `:persist-hard-state`, `:apply-log`)
- [ ] Support for multi-phase voting (CometBFT prevote/precommit)
- [ ] Support for leader election (Raft term management)
- [ ] Support for probabilistic finality (Avalanche confidence)
- [ ] Support for DAG-based consensus (Narwhal certificates)

**Future: Phase 3 - Production Algorithms**

- [ ] CometBFT-style BFT (locking mechanism, valid block tracking)
- [ ] Raft (log replication, persistent hard state)
- [ ] Avalanche (random sampling, confidence accumulation)
- [ ] Narwhal-Bullshark (DAG mempool, leader-based ordering)

## Performance

Benchmarks on consumer hardware (AMD Ryzen):

**Cryptography:**
- ED25519 sign: ~70,000 ops/sec (single core)
- ED25519 verify: ~24,000 ops/sec (single core)

**Consensus (Round-Robin, 3 validators):**
- Single round finalization: < 100ms (mock network)
- Multi-round throughput: 10+ rounds/sec
- Network overhead: +50-200ms (Kabel P2P over localhost)

**Scalability** (not yet optimized):
- Tested: 3-7 validators
- Target: 100+ validators (with sampling-based algorithms)

## Design Principles

1. **Separation of Concerns**
   - Pure state machines (no I/O)
   - Runtime handles effects
   - Network is pluggable

2. **Explicit Over Implicit**
   - Effects as data (not callbacks)
   - State transitions visible
   - No hidden mutations

3. **Testable**
   - Pure functions → easy unit tests
   - Mock network → integration tests
   - Generative tests → edge cases

4. **Flexible**
   - Support multiple algorithms
   - Pluggable components
   - No hardcoded assumptions

## Related Projects

- **[yggdrasil](https://github.com/replikativ/yggdrasil)** - Copy-on-write protocols for heterogeneous systems
- **[kabel](https://github.com/replikativ/kabel)** - P2P communication library (WebSocket-based)
- **[konserve](https://github.com/replikativ/konserve)** - Key-value storage abstraction
- **[datahike](https://github.com/replikativ/datahike)** - Datomic-like database with Yggdrasil protocols
- **[superv.async](https://github.com/replikativ/superv.async)** - Supervised async operations

## References

### Consensus Algorithms

- [CometBFT](https://github.com/cometbft/cometbft) - Byzantine Fault Tolerant consensus (Tendermint successor)
- [Raft Paper](https://raft.github.io/raft.pdf) - Understandable consensus algorithm
- [Avalanche Paper](https://arxiv.org/abs/1906.08936) - Snowflake, Snowball, Avalanche family
- [Narwhal and Tusk](https://arxiv.org/abs/2105.11827) - DAG-based mempool
- [Bullshark](https://arxiv.org/abs/2201.05677) - Simplified DAG consensus

### Theory

- [Parallel Snapshot Isolation](https://plv.mpi-sws.org/transactions/psi-paper.pdf) - Raad, Lahav, Vafeiadis
- [Hybrid Logical Clocks](https://cse.buffalo.edu/~demirbas/publications/hlc.pdf) - Kulkarni et al.
- [Byzantine Agreement](https://people.eecs.berkeley.edu/~luca/cs174/byzantine.pdf) - Lamport et al.

## License

Copyright © 2026 Christian Weilbach

Licensed under the Eclipse Public License 2.0, see [LICENSE](LICENSE).

## Contributing

Contributions welcome! Please:

1. Fork the repository
2. Create a feature branch
3. Add tests for new functionality
4. Ensure all tests pass (`clj -M:test`)
5. Run code formatting (`clj -M:ffix`)
6. Submit a pull request

Join the discussion on [Clojurians Slack #yggdrasil channel](https://clojurians.slack.com/archives/CB7GJAN0L).

---

**"Urd carves runes into Yggdrasil, establishing what has become."**

Just as the Norn inscribes immutable truth into the world tree, Urd coordinates Byzantine Fault Tolerant consensus across distributed copy-on-write systems.
