//! Placeholder for a single trusted sequencer that is also the aggregator. Users reveal `x`
//! to it (over TLS in a real deployment). It enforces the envelope rule, which needs `x`,
//! and proves each batch with auth-air.

use auth_air::air::AuthRecord;
use auth_air::poseidon1::Poseidon1;
use auth_air::prover::prove;

use crate::chain::Chain;
use crate::utxo::{envelope, lock, tag, Lock, Secret, Transfer};

pub struct Sequencer {
    p: Poseidon1,
    records: Vec<AuthRecord>,
    secrets: Vec<Secret>,
}

impl Sequencer {
    pub fn new() -> Self {
        Self { p: Poseidon1::new(), records: Vec::new(), secrets: Vec::new() }
    }

    /// A reveal is accepted only if its envelope is the earliest one for the lock with a valid tag.
    pub fn submit(&mut self, chain: &Chain, t: &Transfer, x: Secret, next: Lock) -> Result<(), &'static str> {
        let l = lock(&self.p, x);
        if chain.balance(l) == 0 {
            return Err("lock holds no coin");
        }
        let c = envelope(&self.p, x, t, next);
        let earliest = chain.envelopes_for(l).find(|&(ci, ti)| tag(&self.p, x, ci) == *ti).map(|(ci, _)| *ci);
        if earliest != Some(c) {
            return Err("not the earliest valid envelope for this lock");
        }
        if self.records.iter().any(|r| r.anchor == l) {
            return Err("lock already in this batch");
        }
        self.records.push(AuthRecord { anchor: l, m: t.encode(), next, c });
        self.secrets.push(x);
        Ok(())
    }

    /// Proves the pending spends and hands the batch to the chain.
    pub fn seal(&mut self, chain: &mut Chain) -> Result<usize, &'static str> {
        if self.records.is_empty() {
            return Ok(0);
        }
        let proof = prove(&self.records, &self.secrets);
        chain.apply_batch(&self.records, &proof)?;
        self.secrets.clear();
        Ok(std::mem::take(&mut self.records).len())
    }
}
