pub const REG_CLOBBER: [&str; 8] = ["r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"];

#[derive(Clone)]
pub struct Context {
    ctx_string: String,
    declarations: Vec<Declare>,
    clobbers: Vec<String>,
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum DeclType {
    Constant,
    Register,
}

#[derive(Clone)]
struct Declare {
    name: String,
    var: String,
    ty: DeclType,
}

impl Context {
    pub fn new() -> Self {
        Context {
            ctx_string: String::new(),
            declarations: Vec::new(),
            clobbers: Vec::new(),
        }
    }

    fn find(&self, name: &str) -> Option<&Declare> {
        self.declarations.iter().find(|item| item.name == name)
    }

    fn append(&mut self, other: &str) {
        self.ctx_string += other;
    }

    pub fn to_string(&self) -> String {
        self.ctx_string.clone()
    }

    fn get_decl_name(&self, name: &str) -> Option<String> {
        self.find(name).map(|d| format!("{{{}}}", d.name))
    }

    pub fn decl_name(&self, name: &str) -> String {
        self.get_decl_name(name).unwrap()
    }

    pub fn decl_name_with_fallback(&self, name: &str, fallback_name: &str) -> String {
        self.get_decl_name(name).unwrap_or_else(|| self.decl_name(fallback_name))
    }

    pub fn add_declaration(&mut self, id: &str, ty: DeclType, var: &str) {
        let declaration = Declare {
                ty,
                name: id.to_string(),
                var: var.to_string(),
            };
        self.declarations.push(declaration);
    }

    pub fn add_buffer(&mut self, extra_reg: usize) {
        self.append(&format!(
            "
                    let mut spill_buffer = core::mem::MaybeUninit::<[u64; {}]>::uninit();",
            extra_reg
        ));
    }

    pub fn add_llvm_asm(&mut self, ctx_string: String) {
        self.append(&format!(
            "
                    unsafe {{
                        llvm_asm!({},",
            ctx_string
        ));
    }

    pub fn add_clobbers<'a>(&mut self, clobbers: impl Iterator<Item = &'a str>) {
        for clobber in clobbers {
            self.add_clobber(clobber)
        }
    }

    pub fn add_clobber(&mut self, clobber: &str) {
        self.clobbers.push(format!("\"{}\"", clobber));
    }

    pub fn build(&mut self) {
        let declarations: String = self.declarations.iter().map(|dec| {
            use DeclType::*;
            match dec.ty {
                Register => format!("\n            {} = in(reg) {},", dec.name, dec.var),
                Constant => format!("\n            {} = const {},", dec.name, dec.var)
            }
        }).collect::<Vec<String>>().join("");
        self.append(&declarations);
        let clobbers = self.clobbers
            .iter()
            .map(|l| format!("out({}) _", l))
            .collect::<Vec<String>>()
            .join(", \n            ");
        self.append(&format!(
            "
                            {},
                        options(att_syntax));
                    }}
                ",
            clobbers
        ));
    }
}
