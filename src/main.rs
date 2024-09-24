use guiso::poly::Poly;

fn main() {
    let p: Poly<i32> = Poly::from_vector(vec![1, 2, 4, 6]);
    let q: Poly<i32> = Poly::from_vector(vec![5, 3]);
    let r: Poly<i32> = &p * &q;
    println!("{p}, {q}, {r}");
}
