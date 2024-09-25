use crate::identity;
use std::ops;

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
    /// Makes a new matrix from an array.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::from([[1,0,0],[0,1,0],[0,0,1]]);
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
