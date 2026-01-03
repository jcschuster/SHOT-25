use egg::{*, rewrite as rw};

define_language! {
    pub enum HOL {
        Symbol(egg::Symbol),

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

// Helper to safely parse rules without panicking
fn try_rewrite(name: &str, lhs: &str, rhs: &str) -> Result<Rewrite<HOL, ()>, String> {
    let p_lhs: Pattern<HOL> = lhs.parse().map_err(|e| format!("Rule '{}' LHS parse error: {}", name, e))?;
    let p_rhs: Pattern<HOL> = rhs.parse().map_err(|e| format!("Rule '{}' RHS parse error: {}", name, e))?;
    Rewrite::new(name, p_lhs, p_rhs).map_err(|e| format!("Rule '{}' error: {}", name, e))
}

fn make_rules() -> Result<Vec<Rewrite<HOL, ()>>, String> {
    let raw_rules = vec![
        ("absorb-and", "(∧∷o⇾o⇾o ?a (∨∷o⇾o⇾o ?a ?b))", "?a"),
        ("absorb-or",  "(∨∷o⇾o⇾o ?a (∨∷o⇾o⇾o ?a ?b))", "?a"),
        ("assoc-and",  "(∧∷o⇾o⇾o ?a (∧∷o⇾o⇾o ?b ?c))", "(∧∷o⇾o⇾o (∧∷o⇾o⇾o ?a ?b) ?c)"),
        ("assoc-or",   "(∨∷o⇾o⇾o ?a (∨∷o⇾o⇾o ?b ?c))", "(∨∷o⇾o⇾o (∨∷o⇾o⇾o ?a ?b) ?c)"),
        ("comm-and",   "(∧∷o⇾o⇾o ?a ?b)",               "(∧∷o⇾o⇾o ?b ?a)"),
        ("comm-eq",    "(= ?a ?b)",                      "(= ?b ?a)"),
        ("comm-equiv", "(≡∷o⇾o⇾o ?a ?b)",               "(≡∷o⇾o⇾o ?b ?a)"),
        ("comm-or",    "(∨∷o⇾o⇾o ?a ?b)",               "(∨∷o⇾o⇾o ?b ?a)"),
        ("demorg-and", "(¬∷o⇾o (∧∷o⇾o⇾o ?a ?b))",       "(∨∷o⇾o⇾o (¬∷o⇾o ?a) (¬∷o⇾o ?b))"),
        ("demorg-or",  "(¬∷o⇾o (∨∷o⇾o⇾o ?a ?b))",       "(∧∷o⇾o⇾o (¬∷o⇾o ?a) (¬∷o⇾o ?b))"),
        ("dist-and",   "(∧∷o⇾o⇾o ?a (∨∷o⇾o⇾o ?b ?c))", "(∨∷o⇾o⇾o (∧∷o⇾o⇾o ?a ?b) (∧∷o⇾o⇾o ?a ?c))"),
        ("dist-or",    "(∨∷o⇾o⇾o ?a (∧∷o⇾o⇾o ?b ?c))", "(∧∷o⇾o⇾o (∨∷o⇾o⇾o ?a ?b) (∨∷o⇾o⇾o ?a ?c))"),
        ("elim-dneg",  "(¬∷o⇾o (¬∷o⇾o ?a))",            "?a"),
        ("elim-imp",   "(⊃∷o⇾o⇾o ?a ?b)",               "(∨∷o⇾o⇾o ?a (¬∷o⇾o ?b))"),
        ("idem-and",   "(∧∷o⇾o⇾o ?a ?a)",               "?a"),
        ("idem-or",    "(∨∷o⇾o⇾o ?a ?a)",               "?a"),
    ];

    let mut rules = Vec::new();
    for (name, lhs, rhs) in raw_rules {
        // If this returns an error, it means the string didn't match the Language definition
        let rw = try_rewrite(name, lhs, rhs)?;
        rules.push(rw);
    }
    Ok(rules)
}

#[rustler::nif]
fn simplify(s: &str) -> String {
    // 1. Safe Parse
    let expr: RecExpr<HOL> = match s.parse() {
        Ok(e) => e,
        Err(e) => return format!("ERROR: Parse failed: {}", e),
    };

    // 2. Safe Rule Construction
    let rules = match make_rules() {
        Ok(r) => r,
        Err(e) => return format!("ERROR: Invalid Rules: {}", e),
    };

    // 3. Run
    let runner = Runner::default().with_expr(&expr).run(&rules);
    
    if runner.roots.is_empty() {
        return "ERROR: No roots".to_string();
    }

    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (_best_cost, best) = extractor.find_best(root);
    
    best.to_string()
}

rustler::init!("Elixir.THOU.Preprocessing.Rewriting");