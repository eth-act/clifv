// `cases! { name { expr; expr; … } … }`: one #[test] per name, each expression's `{:?}` must
// equal the line `name<TAB>value` of EXPECTED at the same position (see gen-expected.sh; the
// generator, expect/src/main.rs, defines `cases!` to print those lines instead).
macro_rules! cases {
    ($($name:ident { $($e:expr;)* })*) => {
        $(
            #[test]
            fn $name() {
                let got: Vec<String> = vec![$(format!("{:?}", $e)),*];
                let srcs: Vec<&str> = vec![$(stringify!($e)),*];
                let want: Vec<&str> = EXPECTED
                    .lines()
                    .filter_map(|l| l.strip_prefix(concat!(stringify!($name), "\t")))
                    .collect();
                assert_eq!(got.len(), want.len(), "number of cases of {}", stringify!($name));
                for i in 0..got.len() {
                    assert_eq!(got[i], want[i], "{}", srcs[i]);
                }
            }
        )*
    };
}
