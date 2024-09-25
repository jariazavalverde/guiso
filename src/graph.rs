use crate::matrix::Matrix;

pub struct Graph<T> {
    matrix: Matrix<T>,
}

impl<T> Graph<T> {}

impl<const V: usize, T> From<[[T; V]; V]> for Graph<T>
where
    T: Clone,
{
    /// Makes a new graph from an array.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let g: Graph<u8> = Graph::from([[1,0,0],[0,1,0],[0,0,1]]);
    /// ```
    fn from(arr: [[T; V]; V]) -> Self {
        Graph {
            matrix: Matrix::from(arr),
        }
    }
}

impl<T> From<Matrix<T>> for Graph<T> {
    /// Makes a new graph from a matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::matrix::Matrix;
    /// use guiso::graph::Graph;
    ///
    /// let i3: Matrix<u8> = Matrix::from([[1,0,0],[0,1,0],[0,0,1]]);
    /// let g: Graph<u8> = Graph::from(i3);
    /// ```
    fn from(matrix: Matrix<T>) -> Self {
        Graph { matrix }
    }
}
