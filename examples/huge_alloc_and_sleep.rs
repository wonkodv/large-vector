use large_vector::LVec;

pub fn main() {
    let mut vec = LVec::<usize>::with_capacity(1024 * 1000 * 1000);
    println!("allocated");

    std::thread::sleep(std::time::Duration::from_millis(10000));

    println!("poking each page");
    unsafe { vec.set_len(vec.capacity()) };
    for i in 0..(vec.capacity() / 4096) {
        vec[i * 4096] = i;
    }
    println!("poked each page");
    std::thread::sleep(std::time::Duration::from_millis(10000));
    println!("done");
}
