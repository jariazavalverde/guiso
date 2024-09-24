use std::{cmp, fmt, ops};

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
    /// let q: Poly<i32> = Poly::from(vec![1, 2, 4]);
    ///
    /// assert_eq!(6, p.get(3));
    /// assert_eq!(0, q.get(3));
    /// ```
    pub fn get(&self, index: usize) -> T
    where
        T: Copy,
        T: Default,
    {
        let default: T = T::default();
        if self.coeff.len() <= index {
            default
        } else {
            self.coeff[index]
        }
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
}

impl<T> fmt::Display for Poly<T>
where
    T: fmt::Display,
    T: Default,
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
        let default: T = T::default();
        let degree: usize = self.degree();
        let mut r: Result<(), fmt::Error>;
        for (index, coeff) in self.coeff.iter().rev().enumerate() {
            let exp: usize = degree - index;
            // do not display null coefficients unless degree of polynomial is zero
            if *coeff != default || degree == 0 {
                // display plus sign if coefficient is positive and it is not the first monomial
                if *coeff > default && exp < degree {
                    r = write!(f, "+");
                    if r.is_err() {
                        return r;
                    }
                }
                // display coefficient
                r = write!(f, "{coeff}");
                if r.is_err() {
                    return r;
                }
                // display exponent if it is not the term independent
                if exp != 0 {
                    r = write!(f, "x^{exp}");
                    if r.is_err() {
                        return r;
                    }
                }
            }
        }
        Result::Ok(())
    }
}

impl<T> From<Vec<T>> for Poly<T>
where
    T: Default,
    T: PartialEq<T>,
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
        let default: T = T::default();
        if coeff.is_empty() {
            return Poly {
                coeff: vec![default],
            };
        }
        while coeff.len() > 1 && coeff[coeff.len() - 1] == default {
            coeff.pop();
        }
        Poly { coeff }
    }
}

impl<T> Into<Vec<T>> for Poly<T>
{
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

impl<'a, T> ops::Add for &'a Poly<T>
where
    T: Copy,
    T: Default,
    T: PartialEq<T>,
    T: ops::Add<Output = T>,
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
        let size: usize = cmp::max(self.coeff.len(), p.coeff.len());
        let mut coeff: Vec<T> = Vec::new();
        for index in 0..size {
            coeff.push(self.get(index) + p.get(index));
        }
        Poly::from(coeff)
    }
}

impl<'a, T> ops::Mul for &'a Poly<T>
where
    T: Copy,
    T: Default,
    T: PartialEq<T>,
    T: ops::Add<Output = T>,
    T: ops::Mul<Output = T>,
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
        let mut coeff: Vec<T> = vec![T::default(); size];
        for (index1, coeff1) in self.coeff.iter().enumerate() {
            for (index2, coeff2) in p.coeff.iter().enumerate() {
                let exp: usize = index1 + index2;
                coeff[exp] = coeff[exp] + *coeff1 * *coeff2;
            }
        }
        Poly::from(coeff)
    }
}
