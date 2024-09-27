use crate::identity;
use crate::matrix::Matrix;
use std::ops;

pub struct Graph<T> {
    matrix: Matrix<T>,
}

impl<T> Graph<T> {
    /// Makes a complete graph with the given vertices.
    /// A complete graph is a graph in which each pair of graph vertices is connected by an edge.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let k3: Graph<u8> = Graph::complete(3);
    ///
    /// for i in 0..3 {
    ///     for j in 0..3 {
    ///         assert_eq!(1, k3[(i,j)]);
    ///     }
    /// }
    /// ```
    pub fn complete(vertices: usize) -> Graph<T>
    where
        T: Clone,
        T: identity::MulIdentity<T>,
    {
        let matrix: Vec<T> = vec![T::one(); vertices * vertices];
        Graph::from(matrix)
    }

    /// Returns the number of vertices of the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// assert_eq!(3, Graph::<u8>::complete(3).vertices());
    /// assert_eq!(5, Graph::<u8>::complete(5).vertices());
    /// ```
    pub fn vertices(&self) -> usize {
        self.matrix.order()
    }
}

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

impl<T> From<Vec<T>> for Graph<T>
where
    T: Clone,
{
    /// Makes a new graph from a vector.
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
    fn from(vector: Vec<T>) -> Self {
        Graph {
            matrix: Matrix::from(vector),
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

impl<T> ops::Index<(usize, usize)> for Graph<T> {
    type Output = T;

    /// Returns the ij-entry from the graph's matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let k3: Graph<u8> = Graph::complete(3);
    ///
    /// assert_eq!(1, k3[(0, 0)]);
    /// ```
    fn index(&self, index: (usize, usize)) -> &Self::Output {
        &self.matrix[index]
    }
}
