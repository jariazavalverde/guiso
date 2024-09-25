pub struct Matrix<T> {
    matrix: Vec<T>,
    order: usize,
}

impl<T> Matrix<T> {
    /// Returns the ij-entry from the matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    ///
    /// let i3: Matrix<u8> = Matrix::from([[1,0,0],[0,1,0],[0,0,1]]);
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
        let mut matrix: Vec<T> = Vec::new();
        for i in 0..N {
            matrix.extend_from_slice(&arr[i]);
        }
        Matrix { matrix, order: N }
    }
}
