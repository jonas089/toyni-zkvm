//! In-memory placeholder chain: the UTXO set, spent locks and an ordered envelope log.
//! An envelope's position is final as soon as it is appended (a stand-in for L1 finality).

use std::collections::{HashMap, HashSet};

use auth_air::air::{padding, AuthRecord};
use auth_air::poseidon1::Poseidon1;
use auth_air::prover::AuthProof;
use auth_air::verifier::verify;

use crate::utxo::{Envelope, Lock, Tag, Transfer};

pub struct Chain {
    utxos: HashMap<Lock, u64>,
    spent: HashSet<Lock>,
    envelopes: Vec<(Lock, Envelope, Tag)>,
}

impl Chain {
    pub fn new(p: &Poseidon1) -> Self {
        // The padding row proves H1(0), which anyone can open: never usable as a lock.
        let spent = HashSet::from([padding(p).0.anchor]);
        Self { utxos: HashMap::new(), spent, envelopes: Vec::new() }
    }

    pub fn mint(&mut self, lock: Lock, amount: u64) {
        assert!(self.is_fresh(lock));
        self.utxos.insert(lock, amount);
    }

    pub fn balance(&self, lock: Lock) -> u64 {
        self.utxos.get(&lock).copied().unwrap_or(0)
    }

    pub fn is_fresh(&self, lock: Lock) -> bool {
        !self.utxos.contains_key(&lock) && !self.spent.contains(&lock)
    }

    /// Anyone may post; junk is harmless because only valid tags count.
    pub fn post_envelope(&mut self, lock: Lock, c: Envelope, t: Tag) {
        self.envelopes.push((lock, c, t));
    }

    pub fn envelopes_for(&self, lock: Lock) -> impl Iterator<Item = (&Envelope, &Tag)> {
        self.envelopes.iter().filter(move |(l, _, _)| *l == lock).map(|(_, c, t)| (c, t))
    }

    /// Verifies the batch proof, checks every spend, then applies all of them or none.
    pub fn apply_batch(&mut self, records: &[AuthRecord], proof: &AuthProof) -> Result<(), &'static str> {
        if !verify(proof, records) {
            return Err("invalid batch proof");
        }
        let (mut inputs, mut outputs) = (HashSet::new(), HashSet::new());
        for r in records {
            let value = *self.utxos.get(&r.anchor).ok_or("input lock holds no coin")?;
            if !inputs.insert(r.anchor) {
                return Err("lock spent twice in one batch");
            }
            if !self.envelopes_for(r.anchor).any(|(c, _)| *c == r.c) {
                return Err("spend has no posted envelope");
            }
            let t = Transfer::decode(&r.m).ok_or("malformed transfer")?;
            if t.amount.checked_add(t.change) != Some(value) {
                return Err("amounts do not add up to the input");
            }
            for out in [t.to, r.next] {
                if !self.is_fresh(out) || !outputs.insert(out) {
                    return Err("output lock is not fresh");
                }
            }
        }
        for r in records {
            let t = Transfer::decode(&r.m).unwrap();
            self.utxos.remove(&r.anchor);
            self.spent.insert(r.anchor);
            for (out, amount) in [(t.to, t.amount), (r.next, t.change)] {
                if amount > 0 {
                    self.utxos.insert(out, amount);
                }
            }
        }
        Ok(())
    }
}
