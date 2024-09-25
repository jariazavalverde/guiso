pub struct Matrix<T> {
    matrix: Vec<T>,
    order: usize,
}

impl Matrix<u8> {
    /// Makes the identity matrix of the given order.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::identity(3);
    /// ```
    pub fn identity(order: usize) -> Matrix<u8> {
        let mut matrix: Vec<u8> = Vec::with_capacity(order * order);
        for i in 0..order {
            for j in 0..order {
                matrix.push(if i == j { 1 } else { 0 });
            }
        }
        Matrix { matrix, order }
    }
}

impl<T> Matrix<T> {
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
