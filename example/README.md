# UTXO example: chain and sequencer design

A runnable sketch of payments on top of the auth engine. The chain and the sequencer are in-memory placeholders, not real
implementations. Its purpose is to pin down the rules a real chain and sequencer have to follow.

```
cargo run --release -p utxo-example
```

## What the engine proves

For every record `(lock, m, next, c)` in a batch, the prover knows a secret `x` with `H1(x) = lock` and
`H2(m, x, next) = c`. The proof is zero-knowledge, so `x` stays hidden from anyone who only sees the proof. Everything else
below is up to the chain and the sequencer.

## UTXO model

- A coin sits under a one-time lock `H1(x)`. Only the holder of `x` can spend it, and only once.
- A spend's message `m` pays `amount` to a recipient's lock and returns `change` to the spend's `next` lock, chosen fresh by
  the spender.
- The chain checks `amount + change` equals the input, that every output lock is fresh, and marks the input spent.
- To receive, you hand out a fresh lock. There is no persistent address.

## Sending a payment: commit, then reveal

1. **Commit.** The spender posts an envelope `(lock, c, t)` with `c = H2(m, x, next)` and a tag `t = H2(c, x, domain)`.
   Nobody can make a valid tag without `x`.
2. **Reveal**, only after the envelope's position is final. The spender gives `(m, x, next)` to the aggregator, who includes
   the spend in the next batch proof.

**Envelope rule:** for each lock, only the earliest envelope with a valid tag can be spent.
- Junk posted before the spender's envelope has no valid tag and is skipped, so nobody can freeze a coin.
- Anyone who learns `x` at reveal can make a valid tag, but only after the spender's envelope is already final.
  A redirect therefore always loses.

The rule is needed because the aggregator learns `x`. Without it, the aggregator could post its own `c` and spend the coin
to itself. An earlier version of the protocol text ("any logged `c` works") had exactly that flaw.

## Trust in the sequencer

Checking the rule needs a fixed order of envelopes, so safety for a payment in flight depends on whoever orders transactions,
on an L1 or an L2:

| Sequencer | Who must be honest | If not |
|---|---|---|
| Distributed, no front-running (order fixed before contents are visible) | honest majority of the sequencer set | in-flight payments can be redirected |
| Single L2 sequencer that posts its order to an L1 | the L1 validator set (finality) | in-flight payments can be redirected |
| Single trusted sequencer, `x` sent over TLS | the sequencer | in-flight payments can be redirected |

In every row a dishonest orderer can redirect payments that are in flight, not just censor them. A signature scheme risks
only censorship there. Coins with nothing in flight are safe in all cases. This is the price of the engine's throughput:
about 11k spends/s, against about 100–200/s for hash-based signatures checked in the same AIR.

**Ideal setup:** a distributed sequencer with no front-running, where order is committed before transaction contents and
secrets become visible (for example, a threshold-encrypted mempool or a commit-then-reveal ordering protocol).

**Acceptable for a trusted-operator deployment:** one centralized sequencer that is also the aggregator, trusted not to
rewrite pending transactions, with `x` sent to it only over TLS. This example models that setup.

## Rules for a real chain

- Enforce the envelope rule. In this example the trusted sequencer checks the tags, because it holds `x`. Without a
  trusted sequencer, the tag check has to move into the proof: the record's tag is valid, and every earlier envelope for
  the lock has an invalid tag. Posting envelopes then needs a fee, since each earlier envelope costs one hash in the proof.
- Reveal `x` only after the envelope's position is final.
- At most one spend per lock per batch, and output locks must be fresh.
- Never accept `H1(0)` as a lock. Batch padding rows prove it, so anyone can open it.
- Bind a chain or deployment identifier into the message, so an envelope cannot be replayed on another deployment.

## What the example mocks

- `chain.rs`: UTXO set, spent locks and an append-only envelope log. Appending counts as final.
- `sequencer.rs`: one trusted sequencer and aggregator. It applies the envelope rule, proves each batch with `auth-air`, and
  hands it to the chain, which verifies the proof and applies every spend or none.
- `main.rs`: Alice and Carol pay Bob in one batch, and Bob pays Alice back in a second. Two attacks are rejected along the
  way: a junk envelope posted ahead of Alice's, and a redirect using Alice's leaked `x`. A replay of a spent lock is
  rejected too.
