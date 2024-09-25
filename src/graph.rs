pub struct Graph<T> {
    matrix: Vec<T>,
    vertices: usize,
}

impl<T> Graph<T> {
    /// Returns the ij-entry of the adjacency matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let g: Graph<u8> = Graph::from([[1,0,0],[0,1,0],[0,0,1]]);
    ///
    /// assert_eq!(1, *g.get(0, 0));
    /// assert_eq!(1, *g.get(1, 1));
    /// assert_eq!(0, *g.get(2, 0));
    /// ```
    pub fn get(&self, row: usize, col: usize) -> &T {
        &self.matrix[row * self.vertices + col]
    }
}

impl<const V: usize, T> From<[[T; V]; V]> for Graph<T>
where
    T: Clone,
{
    /// Makes a new graph from a matrix.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let g: Graph<u8> = Graph::from([[1,0,0],[0,1,0],[0,0,1]]);
    /// ```
    fn from(arr: [[T; V]; V]) -> Self {
        let mut matrix: Vec<T> = Vec::new();
        for i in 0..V {
            matrix.extend_from_slice(&arr[i]);
        }
        Graph {
            matrix,
            vertices: V,
        }
    }
}
