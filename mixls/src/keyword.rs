use mixlib::asm;

pub trait Keyword {
    fn iter() -> impl Iterator<Item = Self>;

    fn as_str(&self) -> &'static str;

    fn docs(&self) -> &'static str;
}

impl Keyword for asm::Op {
    fn iter() -> impl Iterator<Item = Self> {
        Self::iter()
    }

    fn as_str(&self) -> &'static str {
        Self::as_str(*self)
    }

    fn docs(&self) -> &'static str {
        Self::docs(*self)
    }
}

impl Keyword for asm::PseudoOp {
    fn iter() -> impl Iterator<Item = Self> {
        Self::iter()
    }

    fn as_str(&self) -> &'static str {
        Self::as_str(*self)
    }

    fn docs(&self) -> &'static str {
        Self::docs(*self)
    }
}
