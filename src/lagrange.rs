use rayon::prelude::*;
use std::collections::HashMap;

use ark_ec::PrimeGroup;

pub struct LagrangePreprocessed<G> {
    pub g: Vec<G>,
    // For each lagrange polynomial, all 8 bit powers of it
    pub byte_powers: Vec<Vec<G>>,
    // For each lagrange polynomial, all 8 bit powers of it shifted up 8 bits
    pub shifted_byte_powers: Vec<Vec<G>>,
    // Inverse maps
    pub byte_powers_dlog: Vec<HashMap<G, u8>>,
    pub shifted_byte_powers_dlog: Vec<HashMap<G, u8>>,
}

impl<G: PrimeGroup> LagrangePreprocessed<G> {
    pub fn bruteforce_dlog(&self, i: usize, g: G) -> Option<[u8; 2]> {
        for (b0, low_bits) in self.byte_powers[i].iter().enumerate() {
            match self.shifted_byte_powers_dlog[i].get(&(g - low_bits)) {
                None => (),
                Some(b1) => return Some([b0 as u8, *b1]),
            }
        }
        None
    }

    pub fn create(g: Vec<G>) -> Self {
        fn shift_up<G: PrimeGroup>(x: &G) -> G {
            let mut res = x.clone();
            res.double_in_place();
            res.double_in_place();
            res.double_in_place();
            res.double_in_place();
            res.double_in_place();
            res.double_in_place();
            res.double_in_place();
            res.double_in_place();
            res
        }
        println!("hi");

        let byte_powers: Vec<Vec<G>> = g
            .par_iter()
            .map(|g| {
                let mut v = vec![G::zero(), g.clone()];
                for i in 2..256 {
                    v.push(v[i - 1] + g);
                }
                v
            })
            .collect();
        println!("h");
        let shifted_byte_powers = byte_powers
            .par_iter()
            .map(|gs| gs.iter().map(shift_up).collect())
            .collect();
        println!("hacst");
        let byte_powers_dlog = byte_powers
            .par_iter()
            .map(|gs| HashMap::from_iter(gs.iter().enumerate().map(|(i, g)| (*g, i as u8))))
            .collect();

        LagrangePreprocessed {
            g,
            byte_powers_dlog,
            shifted_byte_powers_dlog: byte_powers
                .iter()
                .map(|gs| HashMap::from_iter(gs.iter().enumerate().map(|(i, g)| (*g, i as u8))))
                .collect(),
            byte_powers,
            shifted_byte_powers,
        }
    }
}
