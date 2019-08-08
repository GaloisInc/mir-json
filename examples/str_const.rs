const STR: &'static str = "hello";
const BSTR: &'static [u8; 5] = b"hello";
const BSTR_UNSIZED: &'static [u8] = b"hello";
const ARRAY: [u8; 5] = [b'h', b'e', b'l', b'l', b'o'];
const ARRAY_REF: &[u8; 5] = &[b'h', b'e', b'l', b'l', b'o'];
