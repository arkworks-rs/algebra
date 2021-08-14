use std::fmt;
#[derive(Clone)]
pub struct Context<'a> {
    assembly_instructions: Vec<String>,
    declarations: Vec<Declaration<'a>>,
    used_registers: Vec<Register<'a>>,
}

#[derive(Clone)]
pub enum AssemblyVar {
    Memory(String),
    Variable(String),
    Fixed(String),
}

impl AssemblyVar {
    pub fn memory_access(&self, offset: usize) -> Option<AssemblyVar> {
        match self {
            Self::Variable(a) | Self::Fixed(a) => Some(Self::Memory(format!("{}({})", offset, a))),
            _ => None,
        }
    }

    pub fn memory_accesses(&self, range: usize) -> Vec<AssemblyVar> {
        (0..range)
            .map(|i| {
                let offset = i * 8;
                self.memory_access(offset).unwrap()
            })
            .collect()
    }
}

impl fmt::Display for AssemblyVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Variable(a) | Self::Fixed(a) | Self::Memory(a) => write!(f, "{}", a),
        }
    }
}

impl<'a> From<Declaration<'a>> for AssemblyVar {
    fn from(other: Declaration<'a>) -> Self {
        Self::Variable(format!("{{{}}}", other.name))
    }
}

impl<'a> From<Register<'a>> for AssemblyVar {
    fn from(other: Register<'a>) -> Self {
        Self::Fixed(format!("${}", other.0))
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Register<'a>(pub &'a str);
impl fmt::Display for Register<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "\"{}\"", self.0)
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub enum DeclType {
    Constant,
    Register,
}

#[derive(Copy, Clone)]
pub struct Declaration<'a> {
    /// Name of the assembly template variable declared by `self`.
    name: &'a str,
    /// Rust expression whose value is declared in `self`.
    expr: &'a str,
    /// Type of declaration: Constant (~ immediate) or variable.
    ty: DeclType,
}

impl fmt::Display for Declaration<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self.ty {
            DeclType::Constant => write!(f, "{} = const {},", self.name, self.expr),
            DeclType::Register => write!(f, "{} = in(reg) {},", self.name, self.expr),
        }
    }
}

impl<'a> Context<'a> {
    pub const RAX: Register<'static> = Register("rax");
    pub const RSI: Register<'static> = Register("rsi");
    pub const RCX: Register<'static> = Register("rcx");
    pub const RDX: Register<'static> = Register("rdx");

    pub const R: [Register<'static>; 8] = [
        Register("r8"),
        Register("r9"),
        Register("r10"),
        Register("r11"),
        Register("r12"),
        Register("r13"),
        Register("r14"),
        Register("r15"),
    ];

    pub fn new() -> Self {
        Self {
            assembly_instructions: Vec::new(),
            declarations: Vec::new(),
            used_registers: Vec::new(),
        }
    }

    fn find(&self, name: &str) -> Option<&Declaration<'_>> {
        self.declarations.iter().find(|item| item.name == name)
    }

    fn append(&mut self, other: &str) {
        self.assembly_instructions.push(format!("\"{}\",", other));
    }

    fn instructions_to_string(&self) -> String {
        self.assembly_instructions.join("\n")
    }

    fn get_decl_name(&self, name: &str) -> Option<&Declaration<'_>> {
        self.find(name)
    }

    pub fn get_decl(&self, name: &str) -> Declaration<'_> {
        *self.get_decl_name(name).unwrap()
    }

    pub fn get_decl_with_fallback(&self, name: &str, fallback_name: &str) -> Declaration<'_> {
        self.get_decl_name(name)
            .copied()
            .unwrap_or_else(|| self.get_decl(fallback_name))
    }

    pub fn add_declaration(&mut self, name: &'a str, ty: DeclType, expr: &'a str) {
        let declaration = Declaration { ty, name, expr };
        self.declarations.push(declaration);
    }

    pub fn add_buffer(&mut self, extra_reg: usize) {
        self.append(&format!(
            "let mut spill_buffer = core::mem::MaybeUninit::<[u64; {}]>::uninit();",
            extra_reg
        ));
    }

    pub fn add_asm(&mut self, asm_instructions: &[String]) {
        for instruction in asm_instructions {
            self.append(instruction)
        }
    }

    pub fn add_clobbers(&mut self, clobbers: impl Iterator<Item = Register<'a>>) {
        for clobber in clobbers {
            self.add_clobber(clobber)
        }
    }

    pub fn add_clobber(&mut self, clobber: Register<'a>) {
        self.used_registers.push(clobber);
    }

    pub fn build(self) -> String {
        let declarations: String = self
            .declarations
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<String>>()
            .join("\n");
        let clobbers = self
            .used_registers
            .iter()
            .map(|l| format!("out({}) _", l))
            .collect::<Vec<String>>()
            .join(", \n");
        let options = "options(att_syntax)".to_string();
        let assembly = self.instructions_to_string();
        [
            "unsafe {".to_string(),
            "asm!(".to_string(),
            assembly,
            declarations,
            clobbers,
            options,
            ")".to_string(),
            "}".to_string(),
        ]
        .join("\n")
    }
}
