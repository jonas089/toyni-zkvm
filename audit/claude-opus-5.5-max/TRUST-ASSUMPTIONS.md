# Trust assumption: the sequencer

The auth engine has no signatures. A user authorizes a transaction by giving its one-time secret `x` to whoever builds the
batch proof, the aggregator. That party, and anyone who controls transaction ordering, can try to use `x` for a different
transaction. So the engine's safety depends on the sequencer, whether it runs on an L1 or an L2.

## What the proof guarantees regardless

- A lock can only be spent with its secret, so accounts with no transaction in flight are safe from everyone.
- Each `x` opens its lock once; after that the lock is replaced by `next`.
- The proof is zero-knowledge, so `x` is not visible to anyone who only sees the proof.

## What depends on the sequencer

For a transaction in flight, the party that learns `x` can try to replace it with its own message and its own next lock.
Whether it can succeed depends on the protocol rule and on who orders transactions:

- **Current README rule** ("any logged `c` works", AUTH-04): replacement always succeeds. This rule must not be used.
- **Envelope rule**: the user posts `(lock, c, t = H(x, c))`, and only the earliest envelope with a valid tag can be spent.
  The user reveals `x` only after the envelope's ordering is final. Replacement then requires rewriting that final order.
  This rule is not implemented yet.

Under the envelope rule, safety therefore rests on ordering integrity:

| Sequencer | Who must be honest | Failure mode if not |
|---|---|---|
| Distributed, no front-running (ordering fixed before contents are visible) | honest majority of the sequencer set | in-flight transactions can be replaced |
| Single L2 sequencer that posts its ordering to an L1 | the L1 validator set (finality) | in-flight transactions can be replaced |
| Single trusted sequencer, `x` sent over TLS | the sequencer | in-flight transactions can be replaced |

In every row, a dishonest orderer can steal **in-flight** transactions, not just censor them. A signature scheme only
risks censorship there. This is the price of the engine's throughput: about 11k authorizations/s, versus about 100–200/s
for hash-based signatures checked in the same AIR.

## Recommended setup

- **Ideal:** a distributed sequencer with no front-running, where ordering is committed before transaction contents
  and secrets become visible (for example, a threshold-encrypted mempool or a commit-then-reveal ordering protocol).
  Users reveal `x` only after their envelope's position is final.
- **Acceptable for a trusted-operator deployment:** one centralized sequencer, also acting as the aggregator, that users
  trust not to rewrite their pending transactions, with `x` sent to it only over TLS.

In all setups, the protocol must use the envelope rule rather than the current README rule (AUTH-04).
