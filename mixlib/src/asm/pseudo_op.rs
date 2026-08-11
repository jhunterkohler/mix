macro_rules! define_pseudo_op {
    ($(name = $name:ident, docs = $docs:expr);*;) => {
        /// A MIXAL pseudo-operation.
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub enum PseudoOp {
            $(
                #[doc = $docs]
                $name,
            )*
        }

        impl PseudoOp {
            /// Mnuemonic string.
            pub const fn as_str(&self) -> &'static str {
                match self {
                    $(PseudoOp::$name => stringify!($name),)*
                }
            }

            /// Markdown documentation.
            pub const fn docs(&self) -> &'static str {
                match self {
                    $(PseudoOp::$name => $docs,)*
                }
            }

            /// Iterator through all variants.
            pub fn iter() -> impl Iterator<Item = PseudoOp> {
                const LEN: usize = [$(PseudoOp::$name,)*].len();
                const ALL: [PseudoOp; LEN] = [$(PseudoOp::$name,)*];
                ALL.iter().copied()
            }
        }
    };
}

/// Description of `EQU`.
#[rustfmt::skip]
macro_rules! equ_docs {
    () => {
"`EQU` - Equals To

The symbol in the location field is defined to be the value of the address,
which is a W-value. This takes the place of the usual rule that a symbol in
the location field stands for the current value of the location counter.

Nothing is assembled and the location counter does not move, so an `EQU`
line takes up no room in the program.

Because a W-value may carry a field specification, an equivalent can be made
to depend on the byte size: `BYTESIZE EQU 1(4:4)` defines a symbol whose
value is the byte size itself.

The address may not contain a future reference; every symbol in it must
already have been defined in the location field of an earlier line.
"
    };
}

/// Description of `ORIG`.
#[rustfmt::skip]
macro_rules! orig_docs {
    () => {
"`ORIG` - Origin

The location counter is set to the value of the address, which is a W-value.
Assembly of the lines that follow carries on from there.

A symbol in the location field keeps the value the location counter had
before the change, so `TABLE ORIG *+100` - where `*` stands for the current
value of the counter - names the first of 100 reserved locations.

The address may not contain a future reference; every symbol in it must
already have been defined in the location field of an earlier line.
"
    };
}

/// Description of `CON`.
#[rustfmt::skip]
macro_rules! con_docs {
    () => {
"`CON` - Constant

One word holding the value of the address, which is a W-value, is assembled
into the location the counter names, and the counter then advances by one.

A W-value is a list `E1(F1),…,En(Fn)` of expressions with optional field
specifications, each stored in turn into the named field of a word that
starts out zero; an omitted field means `(0:5)`. So `CON 1000` assembles the
number 1000, while `CON 1000(0:2)` puts 1000 in the address field of an
otherwise empty word.

The address may not contain a future reference; every symbol in it must
already have been defined in the location field of an earlier line.
"
    };
}

/// Description of `ALF`.
#[rustfmt::skip]
macro_rules! alf_docs {
    () => {
"`ALF` - Alphabetical Data

One word holding the MIX character codes of five characters taken from the
address field is assembled into the location the counter names, and the
counter then advances by one. Apart from where its value comes from, `ALF`
behaves exactly like `CON`.

The five characters are taken literally, blanks and all, so the field is
delimited by position rather than by a blank: on a punched card the data
fills columns 17-21, and on a terminal the mnemonic is followed either by
two blanks and five characters, or by one blank and five characters of which
the first is nonblank.
"
    };
}

/// Description of `END`.
#[rustfmt::skip]
macro_rules! end_docs {
    () => {
"`END` - End of Program

The end of the MIXAL program. The address is a W-value whose `(4:5)` field
gives the location of the instruction at which the program is to begin once
it has been loaded.

Just before this line the assembler effectively inserts, in an arbitrary
order, one word for every literal constant used in the program and a
`CON 0` line for every symbol that never appeared in a location field. A
symbol in the location field of the `END` line therefore names the first
location after those inserted words.
"
    };
}

define_pseudo_op! {
    name = EQU,  docs = equ_docs!();
    name = ORIG, docs = orig_docs!();
    name = CON,  docs = con_docs!();
    name = ALF,  docs = alf_docs!();
    name = END,  docs = end_docs!();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pseudo_op_docs_formatting() {
        for op in PseudoOp::iter() {
            assert!(op.docs().ends_with("\n"));
            assert!(op.docs().starts_with(&format!("`{}` - ", op.as_str())));
        }
    }
}
