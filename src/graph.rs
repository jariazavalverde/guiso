pub struct Graph<T> {
    matrix: Vec<T>,
}

impl<T> Graph<T> {
    pub fn from_array<const N: usize>(matrix: [[T; N]; N]) -> Self {
        todo!();
    }
}
