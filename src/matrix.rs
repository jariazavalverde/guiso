use crate::identity;
use crate::poly::Poly;
use std::{cmp, ops};

#[macro_export]
macro_rules! matrix {
    ($($($elem:expr),*);*) => {
        Matrix::from([$([$($elem),*]),*])
    };
}

#[derive(Debug)]
pub struct Matrix<T> {
    matrix: Vec<T>,
    order: usize,
}

impl<T> Matrix<T> {
    /// Makes the identity matrix of the given order.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::identity(3);
    /// ```
    pub fn identity(order: usize) -> Matrix<T>
    where
        T: identity::AddIdentity<T> + identity::MulIdentity<T>,
    {
        let mut matrix: Vec<T> = Vec::with_capacity(order * order);
        for i in 0..order {
            for j in 0..order {
                matrix.push(if i == j { T::one() } else { T::zero() });
            }
        }
        Matrix { matrix, order }
    }

    /// Returns the order of the matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::identity(3);
    ///
    /// assert_eq!(3, i3.order());
    /// ```
    pub fn order(&self) -> usize {
        self.order
    }

    /// Returns the ij-entry from the matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::identity(3);
    ///
    /// assert_eq!(Some(&1), i3.get((0, 0)));
    /// assert_eq!(Some(&0), i3.get((1, 2)));
    /// assert_eq!(None, i3.get((3, 0)));
    /// ```
    pub fn get(&self, index: (usize, usize)) -> Option<&T> {
        let (row, col) = index;
        if row >= self.order || col >= self.order {
            None
        } else {
            self.matrix.get(row * self.order + col)
        }
    }

    pub fn submatrix(&self, row: usize, col: usize) -> Matrix<T>
    where
        T: Clone,
    {
        let mut matrix: Vec<T> = Vec::with_capacity((self.order - 1) * (self.order - 1));
        for i in 0..self.order {
            if i != row {
                for j in 0..self.order {
                    if j != col {
                        matrix.push(self[(i, j)].clone());
                    }
                }
            }
        }
        Matrix {
            matrix,
            order: self.order - 1,
        }
    }

    /// Computes the determinant of the matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix;
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<i32> = Matrix::identity(3);
    /// let a: Matrix<i32> = matrix![1,1,1; 2,1,2; 1,2,4];
    ///
    /// assert_eq!(1, i3.det());
    /// assert_eq!(-3, a.det());
    /// ```
    pub fn det(&self) -> T
    where
        T: Clone,
        T: PartialEq<T>,
        T: identity::AddIdentity<T>,
        T: ops::Neg<Output = T>,
        T: ops::Add<T, Output = T>,
        T: ops::Mul<T, Output = T>,
    {
        if self.order == 0 {
            return T::zero();
        }
        if self.order == 1 {
            return self.matrix[0].clone();
        }
        let zero: T = T::zero();
        let mut det: T = T::zero();
        for index in 0..self.order {
            if self.matrix[index] != zero {
                let mut minor: T = self.submatrix(0, index).det();
                if index % 2 == 0 {
                    minor = -minor;
                }
                det = det + self.matrix[index].clone() * minor;
            }
        }
        det
    }

    pub fn map<F, S>(&self, f: F) -> Matrix<S>
    where
        F: Fn(&T) -> S,
    {
        let mut matrix: Vec<S> = Vec::with_capacity(self.matrix.len());
        for index in 0..self.matrix.len() {
            matrix.push(f(&self.matrix[index]));
        }
        Matrix {
            matrix,
            order: self.order,
        }
    }

    pub fn as_ref(&self) -> Matrix<&T> {
        let mut matrix: Vec<&T> = Vec::with_capacity(self.matrix.len());
        for index in 0..self.matrix.len() {
            matrix.push(&self.matrix[index]);
        }
        Matrix {
            matrix,
            order: self.order,
        }
    }

    /// Computes the characteristic polynomial of the matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::poly::Poly;
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<i8> = Matrix::identity(3);
    ///
    /// assert_eq!(Poly::from(vec![-1,3,-3,1]), i3.char_poly());
    /// ```
    pub fn char_poly<'a>(&'a self) -> Poly<T>
    where
        T: Copy,
        T: PartialEq<T>,
        T: identity::AddIdentity<T>,
        T: identity::MulIdentity<T>,
        T: ops::Neg<Output = T>,
        T: ops::Add<T, Output = T>,
        T: ops::Mul<T, Output = T>,
        &'a T: ops::Mul<&'a T, Output = T>,
    {
        let a: Matrix<Poly<T>> = self.map(|x: &T| Poly::from(vec![-(*x)]));
        let i: Matrix<Poly<T>> = Matrix::identity(self.order());
        let x: Poly<T> = Poly::from(vec![T::zero(), T::one()]);
        (&(&i * &x) + &a).det()
    }
}

impl<const N: usize, T> From<[[T; N]; N]> for Matrix<T>
where
    T: Clone,
{
    /// Makes a new matrix from an array.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::from([[1,0,0],[0,1,0],[0,0,1]]);
    /// ```
    fn from(arr: [[T; N]; N]) -> Self {
        let mut matrix: Vec<T> = Vec::with_capacity(N * N);
        for i in 0..N {
            matrix.extend_from_slice(&arr[i]);
        }
        Matrix { matrix, order: N }
    }
}

impl<T> From<(Vec<T>, usize)> for Matrix<T>
where
    T: Clone,
{
    /// Makes a new matrix from a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::from((vec![1,0,0,0,1,0,0,0,1], 3));
    /// ```
    fn from(v: (Vec<T>, usize)) -> Self {
        let (matrix, order) = v;
        if matrix.len() == order * order {
            Matrix { matrix, order }
        } else {
            Matrix {
                matrix: Vec::new(),
                order: 0,
            }
        }
    }
}

impl<'a, T> ops::Add<&'a Matrix<T>> for &'a Matrix<T>
where
    T: PartialEq<T>,
    &'a T: ops::Add<&'a T, Output = T>,
    T: identity::AddIdentity<T>,
{
    type Output = Matrix<T>;

    /// Returns the sum of two matrices.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix;
    /// use guiso::matrix::Matrix;
    ///
    /// let a: Matrix<u8> = matrix![1,0,2; 1,2,1; 2,1,1];
    /// let b: Matrix<u8> = matrix![0,2,1; 1,0,1; 1,1,0];
    /// let c: Matrix<u8> = matrix![1,2,3; 2,2,2; 3,2,1];
    ///
    /// assert_eq!(c, &a + &b);
    /// ```
    fn add(self, rhs: Self) -> Self::Output {
        if self.order() != rhs.order() {
            panic!("Cannot add matrices with incompatible dimensions.");
        }
        let mut matrix: Vec<T> = Vec::with_capacity(self.matrix.len());
        for i in 0..self.matrix.len() {
            matrix.push(&self.matrix[i] + &rhs.matrix[i]);
        }
        Matrix {
            matrix,
            order: self.order,
        }
    }
}

impl<'a, T> ops::Mul<&'a Matrix<T>> for &'a Matrix<T>
where
    T: PartialEq<T>,
    T: ops::Add<T, Output = T>,
    &'a T: ops::Mul<&'a T, Output = T>,
    T: identity::AddIdentity<T>,
{
    type Output = Matrix<T>;

    /// Returns the product of two matrices.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix;
    /// use guiso::matrix::Matrix;
    ///
    /// let a: Matrix<u8> = matrix![1,0,2; 1,2,1; 2,1,1];
    /// let b: Matrix<u8> = matrix![0,2,1; 1,0,1; 1,1,0];
    /// let c: Matrix<u8> = matrix![2,4,1; 3,3,3; 2,5,3];
    ///
    /// assert_eq!(c, &a * &b);
    /// ```
    fn mul(self, rhs: Self) -> Self::Output {
        if self.order != rhs.order {
            panic!("Cannot multiply matrices with incompatible dimensions.");
        }
        let mut matrix: Vec<T> = Vec::with_capacity(self.matrix.len());
        for i in 0..self.order {
            for j in 0..self.order {
                let mut sum = T::zero();
                for k in 0..self.order {
                    sum = sum + &self[(i, k)] * &rhs[(k, j)];
                }
                matrix.push(sum);
            }
        }
        Matrix {
            matrix,
            order: self.order,
        }
    }
}

impl<'a, T> ops::Mul<&'a T> for &'a Matrix<T>
where
    T: PartialEq<T>,
    &'a T: ops::Mul<&'a T, Output = T>,
    T: identity::AddIdentity<T>,
{
    type Output = Matrix<T>;

    /// Returns the product of a matrix and a scalar.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix;
    /// use guiso::matrix::Matrix;
    ///
    /// let a: Matrix<u8> = matrix![1,0,2; 1,2,1; 2,1,3];
    /// let b: Matrix<u8> = matrix![3,0,6; 3,6,3; 6,3,9];
    ///
    /// assert_eq!(b, &a * &3);
    /// ```
    fn mul(self, rhs: &'a T) -> Self::Output {
        let mut matrix: Vec<T> = Vec::with_capacity(self.matrix.len());
        for index in 0..self.matrix.len() {
            matrix.push(&self.matrix[index] * rhs);
        }
        Matrix {
            matrix,
            order: self.order,
        }
    }
}

impl<T> ops::Index<(usize, usize)> for Matrix<T> {
    type Output = T;

    /// Returns the ij-entry from the matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::identity(3);
    ///
    /// assert_eq!(1, i3[(0, 0)]);
    /// assert_eq!(0, i3[(1, 2)]);
    /// ```
    fn index(&self, index: (usize, usize)) -> &Self::Output {
        let (row, col) = index;
        &self.matrix[row * self.order + col]
    }
}

impl<T> cmp::PartialEq<Matrix<T>> for Matrix<T>
where
    T: PartialEq<T>,
{
    fn eq(&self, other: &Self) -> bool {
        if self.order != other.order {
            return false;
        }
        for i in 0..self.matrix.len() {
            if self.matrix[i] != other.matrix[i] {
                return false;
            }
        }
        true
    }
}
