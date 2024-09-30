pub fn factorial(n: u64) -> u64 {
    (1..=n).product()
}

pub mod combinatorics {

    pub fn binomial(n: u64, k: u64) -> u64 {
        if k > n {
            return 0;
        }
        super::factorial(n) / (super::factorial(k) * super::factorial(n - k))
    }
}
