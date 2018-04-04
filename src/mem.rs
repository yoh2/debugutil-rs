#[macro_export]
macro_rules! dump {
    ($e:expr) => {
        println!("{}:", stringify!($e));
        $crate::mem::dump(&$e);
    };
}

pub fn dump<T>(obj: &T) {
    let size = ::std::mem::size_of::<T>();
    let p = obj as *const T as *const u8;
    let bytes = unsafe { ::std::slice::from_raw_parts(p, size) };
    for (i, b) in bytes.iter().enumerate() {
        match i % 16 {
            0  => print!("{:04x}: {:02x}", i, b),
            8  => print!("  {:02x}", b),
            15 => println!(" {:02x}", b),
            _  => print!(" {:02x}", b),
        }
    }
    if size % 16 != 0 {
        println!();
    }
    println!("{:04x}:", size);
}
