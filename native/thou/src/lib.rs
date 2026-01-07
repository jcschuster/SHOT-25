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

struct OrderedAstSize;

impl CostFunction<HOL> for OrderedAstSize {
    type Cost = (usize, String);

    fn cost<C>(&mut self, enode: &HOL, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = 1;

        let mut total_size = op_cost;
        let mut children_strings = Vec::new();

        enode.for_each(|id| {
            let (size, s) = costs(id);
            total_size += size;
            children_strings.push(s);
        });

        let op_str = match enode {
            HOL::Symbol(s) => s.as_str(),
            HOL::True(_) => "⊤∷o",
            HOL::False(_) => "⊥∷o",
            HOL::And(_) => "∧∷o⇾o⇾o",
            HOL::Or(_) => "∨∷o⇾o⇾o",
            HOL::Not(_) => "¬∷o⇾o",
            HOL::Implies(_) => "⊃∷o⇾o⇾o",
            HOL::Equiv(_) => "≡∷o⇾o⇾o",
            HOL::Eq(_) => "=",
            HOL::Abs(_) => "^",
            HOL::App(_) => "@",
        };

        let self_string = if children_strings.is_empty() {
            op_str.to_string()
        } else {
            format!("({} {})", op_str, children_strings.join(" "))
        };

        let penalty = match enode {
            HOL::And(_) | HOL::Or(_) | HOL::Equiv(_) | HOL::Eq(_) => {
                if children_strings.len() == 2 && children_strings[0] > children_strings[1] {
                    1_000
                } else {
                    0
                }
            }
            _ => 0,
        };

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

fn make_rules() -> Result<Vec<Rewrite<HOL, ()>>, String> {
    let raw_rules = vec![
        ("absorb-and", "(∧∷o⇾o⇾o ?a (∨∷o⇾o⇾o ?a ?b))", "?a"),
        ("absorb-or", "(∨∷o⇾o⇾o ?a (∧∷o⇾o⇾o ?a ?b))", "?a"),
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
        ("comm-and", "(∧∷o⇾o⇾o ?a ?b)", "(∧∷o⇾o⇾o ?b ?a)"),
        ("comm-or", "(∨∷o⇾o⇾o ?a ?b)", "(∨∷o⇾o⇾o ?b ?a)"),
        // commutativity of equivalence and equality leeds to undesired priorities
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
        ("elim-dneg", "(¬∷o⇾o (¬∷o⇾o ?a))", "?a"),
        ("idem-and", "(∧∷o⇾o⇾o ?a ?a)", "?a"),
        ("idem-or", "(∨∷o⇾o⇾o ?a ?a)", "?a"),
        ("neg-f", "(¬∷o⇾o ⊥∷o)", "⊤∷o"),
        ("neg-t", "(¬∷o⇾o ⊤∷o)", "⊥∷o"),
        ("simp-f-and", "(∧∷o⇾o⇾o ?a ⊥∷o)", "⊥∷o"),
        ("simp-f-or", "(∨∷o⇾o⇾o ?a ⊥∷o)", "?a"),
        ("simp-t-and", "(∧∷o⇾o⇾o ?a ⊤∷o)", "?a"),
        ("simp-t-or", "(∨∷o⇾o⇾o ?a ⊤∷o)", "⊤∷o"),
        ("contradict", "(∧∷o⇾o⇾o ?a (¬∷o⇾o ?a))", "⊥∷o"),
        ("exclmiddle", "(∨∷o⇾o⇾o ?a (¬∷o⇾o ?a))", "⊤∷o"),
    ];

    let mut rules = Vec::new();
    for (name, lhs, rhs) in raw_rules {
        let rw = try_rewrite(name, lhs, rhs)?;
        rules.push(rw);
    }
    Ok(rules)
}

#[rustler::nif]
fn simplify(s: &str) -> String {
    let expr: RecExpr<HOL> = match s.parse() {
        Ok(e) => e,
        Err(e) => return format!("ERROR: Parse failed: {}", e),
    };
    let rules = match make_rules() {
        Ok(r) => r,
        Err(e) => return format!("ERROR: Invalid Rules: {}", e),
    };
    let runner = Runner::default().with_expr(&expr).run(&rules);
    if runner.roots.is_empty() {
        return "ERROR: No roots".to_string();
    }
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, OrderedAstSize);
    let (_best_cost, best) = extractor.find_best(root);
    best.to_string()
}

rustler::init!("Elixir.THOU.Preprocessing.Rewriting");
