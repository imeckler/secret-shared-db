use ark_ec::{
    AffineRepr, CurveGroup,
    short_weierstrass::{Affine, SWCurveConfig},
};
use std::collections::HashMap;

pub struct DLogTable<P: SWCurveConfig> {
    pub powers: Vec<Affine<P>>,
    pub table: HashMap<Affine<P>, u16>,
}

// The maqpping i <-> i G
impl<P: SWCurveConfig> DLogTable<P> {
    pub fn bruteforce_dlog(&self, g: &Affine<P>) -> Option<u16> {
        self.table.get(g).copied()
    }

    pub fn from_u16(&self, x: u16) -> Affine<P> {
        self.powers[x as usize]
    }

    pub fn create(g: Affine<P>) -> Self {
        let mut powers = vec![Affine::zero()];
        let g = g.into_group();
        for i in 1..(1 << 16) {
            powers.push((powers[i - 1] + g).into_affine());
        }
        println!("hi {}", powers[59156]);
        DLogTable {
            table: HashMap::from_iter(powers.iter().enumerate().map(|(i, g)| (*g, i as u16))),
            powers,
        }
    }
}
