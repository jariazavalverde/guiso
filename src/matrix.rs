use crate::identity;
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
        if self.order() != rhs.order() {
            panic!("Cannot multiply matrices with incompatible dimensions.");
        }
        let mut matrix: Vec<T> = Vec::with_capacity(self.matrix.len());
        for i in 0..self.order {
            for j in 0..self.order {
                let mut sum = T::zero();
                for k in 0..self.order() {
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
        &self.matrix[row * self.order() + col]
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