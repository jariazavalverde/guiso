use crate::identity::{self, AddIdentity, MulIdentity};
use std::ops;

/// Computes the factorial of a number.
///
/// # Examples
///
/// ```
/// use guiso::math;
///
/// assert_eq!(120u32, math::factorial(5u32));
/// assert_eq!(40320u64, math::factorial(8u64));
/// ```
pub fn factorial<T>(n: T) -> T
where
    T: Clone,
    T: PartialOrd<T>,
    T: AddIdentity<T>,
    T: MulIdentity<T>,
    T: ops::Add<T, Output = T>,
    T: ops::Mul<T, Output = T>,
{
    if identity::is_lt_zero(&n) {
        panic!("Number must be non-negative.");
    }
    let mut factorial: T = T::one();
    let mut m: T = T::one();
    while m <= n {
        factorial = factorial * m.clone();
        m = m + T::one();
    }
    factorial
}

pub mod combinatorics {

    use crate::identity::{self, AddIdentity, MulIdentity};
    use std::ops;

    /// Computes the binomial coefficient C(n,k).
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::math::combinatorics;
    ///
    /// assert_eq!(10u32, combinatorics::binomial(5u32, 2u32));
    /// assert_eq!(56u64, combinatorics::binomial(8u64, 3u64));
    /// ```
    pub fn binomial<T>(n: T, k: T) -> T
    where
        T: Clone,
        T: PartialOrd<T>,
        T: AddIdentity<T>,
        T: MulIdentity<T>,
        T: ops::Add<T, Output = T>,
        T: ops::Sub<T, Output = T>,
        T: ops::Div<T, Output = T>,
        T: ops::Mul<T, Output = T>,
    {
        if n < k {
            panic!("n must be greater than k.");
        }
        if identity::is_lt_zero(&n) {
            panic!("n must be greater than 0.");
        }
        if identity::is_lt_zero(&k) {
            panic!("k must be greater than 0.");
        }
        super::factorial(n.clone())
            / (super::factorial(k.clone()) * super::factorial(n.clone() - k.clone()))
    }
}
