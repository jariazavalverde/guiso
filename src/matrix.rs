use crate::identity;
use crate::poly::Poly;
use std::{cmp, fmt, ops};

///
#[macro_export]
macro_rules! matrix {
    ($($($elem:expr),*);*) => {
        Matrix::from([$([$($elem),*]),*])
    };
}

///
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

    /// Creates the row-based permutation matrix associated to a permutation.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix;
    /// use guiso::matrix::Matrix;
    ///
    /// let p: Matrix<u8> = Matrix::row_permutation([1,3,2]);
    /// let a: Matrix<u8> = matrix![1,0,0; 0,0,1; 0,1,0];
    ///
    /// assert_eq!(a, p);
    /// ```
    pub fn row_permutation<I>(permutation: I) -> Matrix<T>
    where
        T: identity::AddIdentity<T>,
        T: identity::MulIdentity<T>,
        I: IntoIterator<Item = usize>,
    {
        let elems: Vec<usize> = permutation.into_iter().collect();
        let order: usize = elems.len();
        let mut matrix: Vec<T> = Vec::with_capacity(order * order);
        for i in 0..order {
            for j in 0..order {
                matrix.push(if j + 1 == elems[i] {
                    T::one()
                } else {
                    T::zero()
                });
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

    ///
    pub fn submatrix(&self, row: usize, col: usize) -> Matrix<&T> {
        let mut matrix: Vec<&T> = Vec::with_capacity((self.order - 1) * (self.order - 1));
        for i in 0..self.order {
            if i != row {
                for j in 0..self.order {
                    if j != col {
                        matrix.push(&self[(i, j)]);
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
    /// use guiso::matrix::{Matrix};
    ///
    /// let i3: Matrix<i32> = Matrix::identity(3);
    /// let a: Matrix<i32> = matrix![1,1,1; 2,1,2; 1,2,4];
    ///
    /// assert_eq!(1, i3.det());
    /// assert_eq!(-3, a.det());
    /// ```
    pub fn det(&self) -> T
    where
        T: PartialEq<T>,
        T: identity::AddIdentity<T>,
        for<'b> &'b T: ops::Neg<Output = T>,
        for<'b> &'b T: ops::Add<&'b T, Output = T>,
        for<'b> &'b T: ops::Mul<&'b T, Output = T>,
    {
        self.as_ref().det_ref()
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

    /// Converts from `&Matrix<T>` to `Matrix<&T>`.
    ///
    /// # Examples
    ///
    /// This method is used, for example, to compute the determinant of a matrix without taking ownership or cloning data.
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<i32> = Matrix::identity(3);
    /// let det: i32 = i3.as_ref().det_ref();
    ///
    /// assert_eq!(det, i3.det());
    /// ```
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
    {
        let a: Matrix<Poly<T>> = self.map(|x: &T| Poly::from(vec![-*x]));
        let i: Matrix<Poly<T>> = Matrix::identity(self.order());
        let x: Poly<T> = Poly::from(vec![T::zero(), T::one()]);
        (&(&i * &x) + &a).det()
    }
}

impl<'a, T> Matrix<&'a T> {
    ///
    pub fn det_ref(&self) -> T
    where
        T: PartialEq<T>,
        T: identity::AddIdentity<T>,
        for<'b> &'b T: ops::Neg<Output = T>,
        for<'b> &'b T: ops::Add<&'b T, Output = T>,
        for<'b> &'b T: ops::Mul<&'b T, Output = T>,
    {
        let zero: T = T::zero();
        if self.order == 0 {
            return zero;
        }
        if self.order == 1 {
            return self.matrix[0] + &zero;
        }
        let zero: T = T::zero();
        let mut det: T = T::zero();
        for index in 0..self.order {
            if self.matrix[index] != &zero {
                let mut minor: T = self.submatrix_ref(0, index).det_ref();
                if index % 2 == 0 {
                    minor = -&minor;
                }
                det = &det + &(self.matrix[index] * &minor);
            }
        }
        det
    }

    ///
    pub fn submatrix_ref(&self, row: usize, col: usize) -> Matrix<&T> {
        let mut matrix: Vec<&T> = Vec::with_capacity((self.order - 1) * (self.order - 1));
        for i in 0..self.order {
            if i != row {
                for j in 0..self.order {
                    if j != col {
                        matrix.push(self[(i, j)]);
                    }
                }
            }
        }
        Matrix {
            matrix,
            order: self.order - 1,
        }
    }
}

impl<T> fmt::Display for Matrix<T>
where
    T: fmt::Display,
{
    /// Formats the matrix using the given formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix;
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<i32> = Matrix::identity(3);
    /// let a: Matrix<i32> = matrix![111,11; 1111,1];
    ///
    /// assert_eq!("[ [1, 0, 0]\n  [0, 1, 0]\n  [0, 0, 1] ]", format!("{i3}"));
    /// assert_eq!("[ [ 111, 11]\n  [1111,  1] ]", format!("{a}"));
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let format: Vec<String> = self.matrix.iter().map(|x: &T| format!("{x}")).collect();
        let mut width: Vec<usize> = vec![0; self.order];
        // compute max width of each column
        for i in 0..self.order {
            for j in 0..self.order {
                width[j] = cmp::max(width[j], format[i * self.order + j].len());
            }
        }
        // open matrix
        write!(f, "[ ")?;
        for i in 0..self.order {
            // open row
            if i > 0 {
                write!(f, "  ")?;
            }
            write!(f, "[")?;
            // write element
            for j in 0..self.order {
                write!(
                    f,
                    "{:>width$}",
                    format[i * self.order + j],
                    width = width[j]
                )?;
                if j < self.order - 1 {
                    write!(f, ", ")?;
                }
            }
            // close row
            if i < self.order - 1 {
                writeln!(f, "]")?;
            // close matrix
            } else {
                write!(f, "] ]")?;
            }
        }
        Result::Ok(())
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

impl<T> From<Vec<T>> for Matrix<T> {
    /// Makes a new matrix from a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::from(vec![1,0,0,0,1,0,0,0,1]);
    /// ```
    fn from(matrix: Vec<T>) -> Self {
        let order: usize = (matrix.len() as f64).sqrt().floor() as usize;
        if order * order != matrix.len() {
            panic!("Incompatible number of elements.");
        }
        Matrix { matrix, order }
    }
}

impl<'a, T> ops::Add<&'a Matrix<T>> for &'a Matrix<T>
where
    T: PartialEq<T>,
    T: identity::AddIdentity<T>,
    &'a T: ops::Add<&'a T, Output = T>,
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
    T: identity::AddIdentity<T>,
    &'a T: ops::Mul<&'a T, Output = T>,
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
    T: identity::AddIdentity<T>,
    &'a T: ops::Mul<&'a T, Output = T>,
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
    /// Compares two matrices.
    /// Two matrices with the same order are equal when the coefficients of all their entries are equal.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix;
    /// use guiso::matrix::Matrix;
    ///
    /// let a: Matrix<i32> = matrix![1,0,2; 1,2,1; 2,1,3];
    /// let b: Matrix<i32> = matrix![1,0,1; 1,2,1; 2,1,3];
    /// let c: Matrix<i32> = matrix![1,0; 1,2];
    ///
    /// assert_eq!(true, a == a);
    /// assert_eq!(false, a == b);
    /// assert_eq!(false, a == c);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        if self.order != other.order {
            return false;
        }
        for index in 0..self.matrix.len() {
            if self.matrix[index] != other.matrix[index] {
                return false;
            }
        }
        true
    }
}
