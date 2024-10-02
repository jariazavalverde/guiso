use crate::identity;
use crate::math::combinatorics;
use crate::matrix::Matrix;
use std::ops;

///
#[macro_export]
macro_rules! graph {
    ($($($elem:expr),*);*) => {
        Graph::from([$([$($elem),*]),*])
    };
}

///
#[derive(Debug)]
pub struct Graph<T> {
    matrix: Matrix<T>,
}

impl<T> Graph<T> {
    /// Creates a complete graph with the specified vertices.
    ///
    /// A complete graph is a graph in which each pair of graph vertices is connected by an edge.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let k3: Graph<u8> = Graph::complete(3);
    /// ```
    pub fn complete(vertices: usize) -> Graph<T>
    where
        T: identity::AddIdentity<T>,
        T: identity::MulIdentity<T>,
    {
        let mut matrix: Vec<T> = Vec::with_capacity(vertices * vertices);
        for i in 0..vertices {
            for j in 0..vertices {
                matrix.push(if i != j { T::one() } else { T::zero() });
            }
        }
        Graph::from(matrix)
    }

    /// Creates a complete bipartite graph with the specified vertices.
    ///
    /// A complete bipartite graph is a bipartite graph where every vertex of the first set is connected to every vertex of the second set.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let k3_5: Graph<u8> = Graph::biclique(3,5);
    /// ```
    pub fn biclique(n: usize, m: usize) -> Graph<T>
    where
        T: identity::AddIdentity<T>,
        T: identity::MulIdentity<T>,
    {
        let vertices: usize = n + m;
        let mut matrix: Vec<T> = Vec::with_capacity(vertices * vertices);
        for i in 0..vertices {
            for j in 0..vertices {
                matrix.push(if i < n && j >= n || i >= n && j < n {
                    T::one()
                } else {
                    T::zero()
                });
            }
        }
        Graph::from(matrix)
    }

    /// Creates a Johnson graph J(n, k).
    ///
    /// The vertices of the Johnson graph J(n, k) are the k-element subsets of an n-element set.
    /// Two vertices are adjacent when the intersection of the two vertices contains k-1 elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let j5_2: Graph<u8> = Graph::johnson(5,2);
    /// ```
    pub fn johnson(n: usize, k: usize) -> Graph<T>
    where
        T: identity::AddIdentity<T>,
        T: identity::MulIdentity<T>,
    {
        let vertices: usize = combinatorics::binomial(n, k);
        let pow: usize = 2usize.pow(n as u32);
        let k1: u32 = (k - 1) as u32;
        let mut matrix: Vec<T> = Vec::with_capacity(vertices * vertices);
        let k_one_elems: Vec<usize> = (0..pow)
            .filter(|n: &usize| n.count_ones() == k as u32)
            .collect();
        for i in k_one_elems.iter() {
            for j in k_one_elems.iter() {
                matrix.push(if (*i & *j).count_ones() == k1 {
                    T::one()
                } else {
                    T::zero()
                });
            }
        }
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

    /// Returns the adjacency matrix of the graph.
    ///
    /// An adjacency matrix is a square matrix that indicate whether pairs of vertices are adjacent or not in the graph.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let k3: Graph<i32> = Graph::complete(3);
    ///
    /// assert_eq!(3, k3.adjacency().order());
    /// ```
    pub fn adjacency(&self) -> &Matrix<T> {
        &self.matrix
    }

    /// Checks whether two graphs are isospectral.
    ///
    /// Two graphs are considered isospectral if their adjacency matrices share the same set of eigenvalues,
    /// even though the graphs themselves may differ in structure.
    ///
    /// # Examples
    ///
    /// The graphs $C_4$​ (a cycle of 4 nodes) and $K_{2,2}$​ (a complete bipartite graph) are isospectral.
    /// Both graphs share the same spectrum: $\{2,0,0,−2\}$, making them isospectral but non-isomorphic.
    ///
    /// ```
    /// use guiso::graph;
    /// use guiso::graph::Graph;
    ///
    /// let c4: Graph<i8> = graph![0,1,0,1; 1,0,1,0; 0,1,0,1; 1,0,1,0];
    /// let k2_2: Graph<i8> = graph![0,0,1,1; 0,0,1,1; 1,1,0,0; 1,1,0,0];
    ///
    /// assert_eq!(true, c4.isospectral(&k2_2));
    /// ```
    pub fn isospectral(&self, g: &Graph<T>) -> bool
    where
        T: Clone,
        T: PartialEq<T>,
        T: identity::AddIdentity<T>,
        T: identity::MulIdentity<T>,
        T: ops::Neg<Output = T>,
        T: ops::Add<T, Output = T>,
        T: ops::Mul<T, Output = T>,
    {
        self.matrix.char_poly() == g.matrix.char_poly()
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
    /// let k3: Graph<u8> = Graph::from([[1,0,0],[0,1,0],[0,0,1]]);
    ///
    /// assert_eq!(3, k3.vertices());
    /// ```
    fn from(arr: [[T; V]; V]) -> Self {
        Graph {
            matrix: Matrix::from(arr),
        }
    }
}

impl<T> From<Vec<T>> for Graph<T> {
    /// Makes a new graph from a vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use guiso::graph::Graph;
    ///
    /// let k3: Graph<i8> = Graph::from(vec![1,0,0,0,1,0,0,0,1]);
    ///
    /// assert_eq!(3, k3.vertices());
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
    /// let i3: Matrix<u8> = Matrix::identity(3);
    /// let g: Graph<u8> = Graph::from(i3);
    ///
    /// assert_eq!(3, g.vertices());
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
    /// assert_eq!(0, k3[(0, 0)]);
    /// ```
    fn index(&self, index: (usize, usize)) -> &Self::Output {
        &self.matrix[index]
    }
}
