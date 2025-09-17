use ark_ff::Field;

pub struct Pows<F> {
    acc: F,
    base: F,
}

impl<F: Field> Iterator for Pows<F> {
    type Item = F;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.acc;
        self.acc *= self.base;
        Some(res)
    }
}

pub fn pows<F: Field>(x: F) -> Pows<F> {
    Pows {
        acc: F::one(),
        base: x,
    }
}


