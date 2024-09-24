pub struct Graph<T> {
    matrix: Vec<T>,
    vertices: usize,
}

impl<T> Graph<T> {}

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
    /// let g: Graph<u8> = Graph::from([[1,0,0],[0,1,0],[0,0,0]]);
    /// ```
    fn from(arr: [[T; V]; V]) -> Self {
        let mut matrix: Vec<T> = Vec::new();
        for i in 1..V {
            matrix.extend_from_slice(&arr[i]);
        }
        Graph {
            matrix,
            vertices: V,
        }
    }
}
