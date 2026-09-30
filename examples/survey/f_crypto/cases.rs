cases! {
    chacha {
        chacha_quarter_round(bb(0x1111_1111), bb(0x0102_0304), bb(0x9b8d_6f43), bb(0x0123_4567));
        {
            let key = [0x0302_0100, 0x0706_0504, 0x0b0a_0908, 0x0f0e_0d0c, 0x1312_1110, 0x1716_1514, 0x1b1a_1918, 0x1f1e_1d1c];
            let mut out = [0u8; 64];
            chacha20_block(bb(&key), bb(1), bb(&[0x0900_0000, 0x4a00_0000, 0]), bb(&mut out));
            out
        };
    }
    sha256 {
        {
            // SHA-256("abc"): the padded single block
            let mut block = [0u8; 64];
            block[..3].copy_from_slice(b"abc");
            block[3] = 0x80;
            block[63] = 24;
            let mut state = [0x6a09_e667, 0xbb67_ae85, 0x3c6e_f372, 0xa54f_f53a, 0x510e_527f, 0x9b05_688c, 0x1f83_d9ab, 0x5be0_cd19];
            sha256_compress(bb(&mut state), bb(&block));
            state
        };
    }
    constant_time { ct_eq(bb(&[7; 32]), bb(&[7; 32])); { let mut b = [7; 32]; b[31] = 6; ct_eq(bb(&[7; 32]), bb(&b)) }; }
}
