use crate::identity;
use std::{cmp, fmt, ops};

///
#[macro_export]
macro_rules! poly {
    ($($data:expr),*) => {
        Poly::from(vec![$($data),*])
    };
}

///
#[derive(Debug)]
pub struct Poly<T> {
    coeff: Vec<T>,
}

impl<T> Poly<T> {
    /// Returns the coefficient of the monomial with the given degree.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![1, 2, 4, 0]);
    /// let r: Poly<i32> = Poly::from(vec![1, 2, 4]);
    ///
    /// assert_eq!(Some(&6), p.get(3));
    /// assert_eq!(None, q.get(3));
    /// assert_eq!(None, r.get(3));
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        self.coeff.get(index)
    }

    /// Returns the degree of the polynomial.
    /// Degree of a polynomial is the highest of the degrees of the polynomial's monomials with non-zero coefficients.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![1, 2, 4, 0]);
    ///
    /// assert_eq!(3, p.degree());
    /// assert_eq!(2, q.degree());
    /// ```
    pub fn degree(&self) -> usize {
        self.coeff.len() - 1
    }

    /// Returns the product of a scalar and a polynomial.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![5, 10, 20, 30]);
    ///
    /// assert_eq!(q, p.scalar(5));
    /// ```
    pub fn scalar(&self, scalar: T) -> Self
    where
        T: Copy,
        T: PartialEq<T>,
        T: ops::Mul<T, Output = T>,
        T: identity::AddIdentity<T>,
    {
        let mut coeff: Vec<T> = Vec::with_capacity(self.coeff.len());
        for elem in self.coeff.iter() {
            coeff.push(scalar * *elem);
        }
        Poly::from(coeff)
    }
}

impl<T> fmt::Display for Poly<T>
where
    T: fmt::Display,
    T: identity::AddIdentity<T>,
    T: PartialOrd<T>,
{
    /// Formats the polynomial using the given formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![1, 0, 5, 0, -9]);
    /// let r: Poly<i32> = Poly::from(vec![]);
    ///
    /// assert_eq!("6x^3+4x^2+2x^1+1", format!("{p}"));
    /// assert_eq!("-9x^4+5x^2+1", format!("{q}"));
    /// assert_eq!("0", format!("{r}"));
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let zero: T = T::zero();
        let degree: usize = self.degree();
        for (index, coeff) in self.coeff.iter().rev().enumerate() {
            let exp: usize = degree - index;
            // do not display null coefficients unless degree of polynomial is zero
            if *coeff != zero || degree == 0 {
                // display plus sign if coefficient is positive and it is not the first monomial
                if *coeff > zero && exp < degree {
                    write!(f, "+")?;
                }
                // display coefficient
                write!(f, "{coeff}")?;
                // display exponent if it is not the term independent
                if exp != 0 {
                    write!(f, "x^{exp}")?;
                }
            }
        }
        Result::Ok(())
    }
}

impl<T> From<Vec<T>> for Poly<T>
where
    T: PartialEq<T>,
    T: identity::AddIdentity<T>,
{
    /// Makes a new polynomial from a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// ```
    fn from(mut coeff: Vec<T>) -> Self {
        let zero: T = T::zero();
        if coeff.is_empty() {
            return Poly { coeff: vec![zero] };
        }
        while coeff.len() > 1 && coeff[coeff.len() - 1] == zero {
            coeff.pop();
        }
        Poly { coeff }
    }
}

impl<T> Into<Vec<T>> for Poly<T> {
    /// Returns the coefficients of the monomials as a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![1, 2, 4, 0]);
    /// let v: Vec<i32> = p.into();
    /// let w: Vec<i32> = q.into();
    ///
    /// assert_eq!(vec![1, 2, 4, 6], v);
    /// assert_eq!(vec![1, 2, 4], w);
    /// ```
    fn into(self) -> Vec<T> {
        self.coeff
    }
}

impl<T> ops::Add<Poly<T>> for Poly<T>
where
    T: Copy,
    T: PartialEq<T>,
    T: ops::Add<T, Output = T>,
    T: identity::AddIdentity<T>,
{
    type Output = Poly<T>;

    /// Returns the sum of two polynomials.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![5, 3]);
    /// let r: Poly<i32> = Poly::from(vec![6, 5, 4, 6]);
    ///
    /// assert_eq!(r, p + q);
    /// ```
    fn add(self, p: Self) -> Self::Output {
        &self + &p
    }
}

impl<'a, T> ops::Add<&'a Poly<T>> for &'a Poly<T>
where
    T: Copy,
    T: PartialEq<T>,
    T: ops::Add<T, Output = T>,
    T: identity::AddIdentity<T>,
{
    type Output = Poly<T>;

    /// Returns the sum of two polynomials.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![5, 3]);
    /// let r: Poly<i32> = &p + &q;
    /// let v: Vec<i32> = r.into();
    ///
    /// assert_eq!(vec![6, 5, 4, 6], v);
    /// ```
    fn add(self, p: Self) -> Self::Output {
        let greater: &Poly<T>;
        let smaller: &Poly<T>;
        if self.degree() >= p.degree() {
            greater = self;
            smaller = p;
        } else {
            greater = p;
            smaller = self;
        }
        let size: usize = cmp::max(greater.coeff.len(), smaller.coeff.len());
        let mut coeff: Vec<T> = Vec::with_capacity(size);
        for index in 0..greater.coeff.len() {
            coeff.push(greater[index]);
        }
        for index in 0..smaller.coeff.len() {
            coeff[index] = coeff[index] + smaller[index];
        }
        Poly::from(coeff)
    }
}

impl<T> ops::Mul<Poly<T>> for Poly<T>
where
    T: Copy,
    T: PartialEq<T>,
    T: ops::Add<T, Output = T>,
    T: ops::Mul<T, Output = T>,
    T: identity::AddIdentity<T>,
{
    type Output = Poly<T>;

    /// Returns the product of two polynomials.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![5, 3]);
    /// let r: Poly<i32> = Poly::from(vec![5, 13, 26, 42, 18]);
    ///
    /// assert_eq!(r, p * q);
    /// ```
    fn mul(self, p: Self) -> Self::Output {
        &self * &p
    }
}

impl<'a, T> ops::Mul<&'a Poly<T>> for &'a Poly<T>
where
    T: Copy,
    T: PartialEq<T>,
    T: ops::Add<T, Output = T>,
    T: ops::Mul<T, Output = T>,
    T: identity::AddIdentity<T>,
{
    type Output = Poly<T>;

    /// Returns the product of two polynomials.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![5, 3]);
    /// let r: Poly<i32> = &p * &q;
    /// let v: Vec<i32> = r.into();
    ///
    /// assert_eq!(vec![5, 13, 26, 42, 18], v);
    /// ```
    fn mul(self, p: Self) -> Self::Output {
        let size: usize = self.coeff.len() * p.coeff.len();
        let mut coeff: Vec<T> = vec![T::zero(); size];
        for (index1, coeff1) in self.coeff.iter().enumerate() {
            for (index2, coeff2) in p.coeff.iter().enumerate() {
                let exp: usize = index1 + index2;
                coeff[exp] = coeff[exp] + *coeff1 * *coeff2;
            }
        }
        Poly::from(coeff)
    }
}

impl<'a, T> ops::Mul<T> for &'a Poly<T>
where
    T: Copy,
    T: PartialEq<T>,
    T: ops::Mul<T, Output = T>,
    T: identity::AddIdentity<T>,
{
    type Output = Poly<T>;

    /// Returns the product of a polynomial and a scalar.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![5, 10, 20, 30]);
    ///
    /// assert_eq!(q, &p * 5);
    /// ```
    fn mul(self, scalar: T) -> Self::Output {
        let mut coeff: Vec<T> = Vec::with_capacity(self.coeff.len());
        for elem in self.coeff.iter() {
            coeff.push(*elem * scalar);
        }
        Poly::from(coeff)
    }
}

impl<T> ops::Neg for Poly<T>
where
    T: Copy,
    T: ops::Neg<Output = T>,
{
    type Output = Poly<T>;

    ///
    fn neg(self) -> Self::Output {
        -&self
    }
}

impl<'a, T> ops::Neg for &'a Poly<T>
where
    T: Copy,
    T: ops::Neg<Output = T>,
{
    type Output = Poly<T>;

    ///
    fn neg(self) -> Self::Output {
        let mut coeff: Vec<T> = Vec::with_capacity(self.coeff.len());
        for index in 0..self.coeff.len() {
            coeff.push(-self.coeff[index]);
        }
        Poly { coeff }
    }
}

impl<T> ops::Index<usize> for Poly<T> {
    type Output = T;

    /// Returns the coefficient of the monomial with the given degree.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    ///
    /// assert_eq!(6, p[3]);
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        &self.coeff[index]
    }
}

impl<T> cmp::PartialEq<Poly<T>> for Poly<T>
where
    T: PartialEq<T>,
{
    /// Compares two polynomials.
    /// Two polynomials with the same order are equal when the coefficients of all their monomials are equal.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    ///
    /// let p: Poly<i32> = Poly::from(vec![1, 2, 4, 6]);
    /// let q: Poly<i32> = Poly::from(vec![1, 2, 4, 6, 0, 0]);
    /// let r: Poly<i32> = Poly::from(vec![3, 2, 4, 6]);
    /// let s: Poly<i32> = Poly::from(vec![2, 4, 6]);
    ///
    /// assert_eq!(true, p == p);
    /// assert_eq!(true, p == q);
    /// assert_eq!(false, p == r);
    /// assert_eq!(false, p == s);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        if self.coeff.len() != other.coeff.len() {
            return false;
        }
        for index in 0..self.coeff.len() {
            if self.coeff[index] != other.coeff[index] {
                return false;
            }
        }
        true
    }
}

impl<T> identity::AddIdentity<Poly<T>> for Poly<T>
where
    T: identity::AddIdentity<T>,
    T: PartialEq<T>,
{
    fn zero() -> Poly<T> {
        poly![T::zero()]
    }
}

impl<T> identity::MulIdentity<Poly<T>> for Poly<T>
where
    T: PartialEq<T>,
    T: identity::AddIdentity<T>,
    T: identity::MulIdentity<T>,
{
    fn one() -> Poly<T> {
        poly![T::one()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Polynomials never should be empty.
    #[test]
    fn poly_non_empty() {
        let empty: Poly<i32> = poly![];
        let non_empty: Poly<i32> = poly![1, 2, 3];
        assert_ne!(0, empty.coeff.len());
        assert_ne!(0, non_empty.coeff.len());
    }

    // Last coefficient of a polynomial never should be zero unless polynomial is null.
    #[test]
    fn poly_last_monomial_non_zero() {
        let empty: Poly<i32> = poly![];
        let non_empty: Poly<i32> = poly![1, 2, 3, 0, 0, 0];
        assert_eq!(0, empty[empty.coeff.len() - 1]);
        assert_ne!(0, non_empty[non_empty.coeff.len() - 1]);
    }

    // Addition should be commutative for polynomials with coefficients in a ring.
    #[test]
    fn poly_add_commutativity() {
        let p: Poly<i32> = poly![1, -3, 0, 4, -2];
        let q: Poly<i32> = poly![8, 0, -1, -2];
        assert_eq!(&p + &q, &q + &p);
    }

    // Addition should be associative for polynomials with coefficients in a ring.
    #[test]
    fn poly_add_associativity() {
        let p: Poly<i32> = poly![1, -3, 0, 4, -2];
        let q: Poly<i32> = poly![8, 0, -1, -2];
        let r: Poly<i32> = poly![1, 0, 0, -4, 2];
        assert_eq!(&p + &(&q + &r), &(&p + &q) + &r);
    }

    // Multiplication should be associative for polynomials with coefficients in a ring.
    #[test]
    fn poly_mul_associativity() {
        let p: Poly<i32> = poly![1, -3, 0, 4, -2];
        let q: Poly<i32> = poly![8, 0, -1, -2];
        let r: Poly<i32> = poly![1, 0, 0, -4, 2];
        assert_eq!(&p * &(&q * &r), &(&p * &q) * &r);
    }

    // Multiplication should be distributive w.r.t. addition for polynomials with coefficients in a ring.
    #[test]
    fn poly_mul_distributivity() {
        let p: Poly<i32> = poly![1, -3, 0, 4, -2];
        let q: Poly<i32> = poly![8, 0, -1, -2];
        let r: Poly<i32> = poly![1, 0, 0, -4, 2];
        assert_eq!(&p * &(&q + &r), &(&p * &q) + &(&p * &r));
        assert_eq!(&(&q + &r) * &p, &(&q * &p) + &(&r * &p));
    }
}
