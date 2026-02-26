use egg::*;

define_language! {
    pub enum HOL {
        Symbol(egg::Symbol),

        "⊤∷o"      = True([Id; 0]),
        "⊥∷o"      = False([Id; 0]),
        "∧∷o⇾o⇾o" = And([Id; 2]),
        "∨∷o⇾o⇾o" = Or([Id; 2]),
        "¬∷o⇾o"   = Not(Id),
        "⊃∷o⇾o⇾o" = Implies([Id; 2]),
        "≡∷o⇾o⇾o" = Equiv([Id; 2]),
        "="        = Eq([Id; 2]),

        "^" = Abs([Id; 2]),
        "@" = App([Id; 2]),
    }
}

#[derive(PartialEq)]
enum Mode {
    Simplify,
    Orient,
}

struct OrderedAstSize;

impl CostFunction<HOL> for OrderedAstSize {
    type Cost = (usize, String);

    fn cost<C>(&mut self, enode: &HOL, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let mut total_size = 1;
        let mut children_strings = Vec::new();

        enode.for_each(|id| {
            let (size, s) = costs(id);
            total_size += size;
            children_strings.push(s);
        });

        let op_str = match enode {
            HOL::Symbol(s) => s.as_str().to_string(),
            HOL::True(_) => "⊤∷o".to_string(),
            HOL::False(_) => "⊥∷o".to_string(),
            HOL::And(_) => "∧∷o⇾o⇾o".to_string(),
            HOL::Or(_) => "∨∷o⇾o⇾o".to_string(),
            HOL::Not(_) => "¬∷o⇾o".to_string(),
            HOL::Implies(_) => "⊃∷o⇾o⇾o".to_string(),
            HOL::Equiv(_) => "≡∷o⇾o⇾o".to_string(),
            HOL::Eq(_) => "=".to_string(),
            HOL::Abs(_) => "^".to_string(),
            HOL::App(_) => "@".to_string(),
        };

        let self_string = if children_strings.is_empty() {
            op_str
        } else {
            format!("({} {})", op_str, children_strings.join(" "))
        };

        let penalty = matches!(enode, HOL::And(_) | HOL::Or(_) | HOL::Equiv(_) | HOL::Eq(_))
            .then(|| {
                (children_strings.len() == 2 && children_strings[0] > children_strings[1])
                    .then_some(1_000)
                    .unwrap_or(0)
            })
            .unwrap_or(0);

        (total_size + penalty, self_string)
    }
}

// safely parse rules without panicking
fn try_rewrite(name: &str, lhs: &str, rhs: &str) -> Result<Rewrite<HOL, ()>, String> {
    let p_lhs: Pattern<HOL> = lhs
        .parse()
        .map_err(|e| format!("Rule '{}' LHS parse error: {}", name, e))?;
    let p_rhs: Pattern<HOL> = rhs
        .parse()
        .map_err(|e| format!("Rule '{}' RHS parse error: {}", name, e))?;
    Rewrite::new(name, p_lhs, p_rhs).map_err(|e| format!("Rule '{}' error: {}", name, e))
}

const COMMON_RULES: &[(&str, &str, &str)] = &[
    //----- commutativity -----//
    ("comm-and", "(∧∷o⇾o⇾o ?a ?b)", "(∧∷o⇾o⇾o ?b ?a)"),
    ("comm-or", "(∨∷o⇾o⇾o ?a ?b)", "(∨∷o⇾o⇾o ?b ?a)"),
    //----- associativity -----//
    (
        "assoc-and",
        "(∧∷o⇾o⇾o ?a (∧∷o⇾o⇾o ?b ?c))",
        "(∧∷o⇾o⇾o (∧∷o⇾o⇾o ?a ?b) ?c)",
    ),
    (
        "assoc-or",
        "(∨∷o⇾o⇾o ?a (∨∷o⇾o⇾o ?b ?c))",
        "(∨∷o⇾o⇾o (∨∷o⇾o⇾o ?a ?b) ?c)",
    ),
];

const SIMP_RULES: &[(&str, &str, &str)] = &[
    //----- De Morgan rules -----//
    (
        "demorg-and",
        "(¬∷o⇾o (∧∷o⇾o⇾o ?a ?b))",
        "(∨∷o⇾o⇾o (¬∷o⇾o ?a) (¬∷o⇾o ?b))",
    ),
    (
        "demorg-or",
        "(¬∷o⇾o (∨∷o⇾o⇾o ?a ?b))",
        "(∧∷o⇾o⇾o (¬∷o⇾o ?a) (¬∷o⇾o ?b))",
    ),
    //----- simplification rules -----//
    ("absorb-and", "(∧∷o⇾o⇾o ?a (∨∷o⇾o⇾o ?a ?b))", "?a"),
    ("absorb-or", "(∨∷o⇾o⇾o ?a (∧∷o⇾o⇾o ?a ?b))", "?a"),
    ("contradict", "(∧∷o⇾o⇾o ?a (¬∷o⇾o ?a))", "⊥∷o"),
    ("elim-dneg", "(¬∷o⇾o (¬∷o⇾o ?a))", "?a"),
    ("exclmiddle", "(∨∷o⇾o⇾o ?a (¬∷o⇾o ?a))", "⊤∷o"),
    ("idem-and", "(∧∷o⇾o⇾o ?a ?a)", "?a"),
    ("idem-or", "(∨∷o⇾o⇾o ?a ?a)", "?a"),
    ("neg-f", "(¬∷o⇾o ⊥∷o)", "⊤∷o"),
    ("neg-t", "(¬∷o⇾o ⊤∷o)", "⊥∷o"),
    ("simp-f-and", "(∧∷o⇾o⇾o ?a ⊥∷o)", "⊥∷o"),
    ("simp-f-or", "(∨∷o⇾o⇾o ?a ⊥∷o)", "?a"),
    ("simp-t-and", "(∧∷o⇾o⇾o ?a ⊤∷o)", "?a"),
    ("simp-t-or", "(∨∷o⇾o⇾o ?a ⊤∷o)", "⊤∷o"),
];

fn make_rules(mode: Mode) -> Result<Vec<Rewrite<HOL, ()>>, String> {
    let rules = if mode == Mode::Simplify {
        COMMON_RULES.iter().chain(SIMP_RULES)
    } else {
        COMMON_RULES.iter().chain([].iter())
    };

    rules
        .map(|(name, lhs, rhs)| try_rewrite(name, lhs, rhs))
        .collect()
}

fn run_egg_on_expr(expr: RecExpr<HOL>, rules: Vec<Rewrite<HOL, ()>>) -> String {
    let runner = Runner::default().with_expr(&expr).run(&rules);
    let root = match runner.roots.first() {
        Some(&r) => r,
        None => return "ERROR: No roots".to_string(),
    };
    let extractor = Extractor::new(&runner.egraph, OrderedAstSize);
    let (_best_cost, best) = extractor.find_best(root);
    best.to_string()
}

fn process_expr(s: &str, mode: Mode) -> String {
    let expr: RecExpr<HOL> = match s.parse() {
        Ok(e) => e,
        Err(e) => return format!("ERROR: Parse failed: {}", e),
    };
    let rules = match make_rules(mode) {
        Ok(r) => r,
        Err(e) => return format!("ERROR: Invalid Rules: {}", e),
    };
    run_egg_on_expr(expr, rules)
}

#[rustler::nif]
fn egg_simplify(s: &str) -> String {
    process_expr(s, Mode::Simplify)
}

#[rustler::nif]
fn egg_simplify_ac(s: &str) -> String {
    process_expr(s, Mode::Orient)
}

rustler::init!("Elixir.SHOT25.Preprocessing.Rewriting");
