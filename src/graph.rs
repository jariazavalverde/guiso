pub struct Graph<T, const N: usize> {
    matrix: [[T; N]; N],
}

impl<T, const N: usize> Graph<T, N> {

    pub fn from_array(matrix: [[T; N]; N]) -> Self {
        Graph { matrix }
    }

}