use z3::{ast::{
    Bool,
    Ast,
    Int,
    Dynamic,
}, Context, Config, SatResult, FuncDecl, Sort, Solver};



fn main() {
    de_morgan();
    prove_example1();
    prove_example2();
}


fn de_morgan() {
    println!("De Morgan Example");
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x1 = Bool::new_const(&ctx, "x1");
    let x2 = Bool::new_const(&ctx, "x2");
    let x_vec = [&x1, &x2];
    let x3 = z3::ast::Bool::and(&ctx, &x_vec);
    let x4 = &x3.not();
    let x5 = &x1.not();
    let x6 = &x2.not();
    let x7 = z3::ast::Bool::or(&ctx, &[&x5, &x6]);
    let s = z3::Solver::new(&ctx);

    let conjecture = &x4._eq(&x7);

    s.assert(&conjecture.not());

    println!("{}\n", s.check() == z3::SatResult::Unsat);
}


fn prove_example1() {
    println!("prove_example1");
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let  x = Int::new_const(&ctx, "x");
    let  y = Int::new_const(&ctx, "y");
    let int_sort = Sort::int(&ctx);
    let  g = FuncDecl::new(&ctx, "g", &[&int_sort], &int_sort);

    let  solver = Solver::new(&ctx);
    let conjecture1 =
        Bool::implies(
            &Int::_eq(
                &x,
                &y),
            &Int::_eq(
                &(g.apply(&[&Dynamic::from(x.clone())]).as_int()).unwrap(),
                &(g.apply(&[&Dynamic::from(y.clone())]).as_int()).unwrap()
            )
        );

    solver.assert(&conjecture1.not());


    if solver.check() == SatResult::Unsat {
        println!("x == y -> g(x) == g(y) Proved\n");
    } else {
        println!("x == y -> g(x) == g(y) Failed to Prove\n");
    }

    solver.reset();

    let g_of_g_of_x = g.apply(&[&g.apply(&[ &Dynamic::from(x.clone()) ] )]).as_int().unwrap();
    let g_of_y = g.apply(&[&Dynamic::from(y.clone())]).as_int().unwrap();

    let conjecture2 = Bool::implies(
        &x._eq(&y),
        &Int::_eq(
            &g_of_g_of_x,
            &g_of_y
        )
    );

    solver.assert(&conjecture2.not());

    if solver.check() == SatResult::Unsat {
        println!("x == y -> g(g(x)) == g(y) is Proved\n");
    } else {
        println!("x == y -> g(g(x)) == g(y) is Failed to Prove\n");
        let model = solver.get_model().unwrap();

        println!("Counter Example:\n{}\n", model);
        println!("g(g(x)) = {}\n", model.eval(&g_of_g_of_x).unwrap());
        println!("g(y) = {}\n", model.eval(&g_of_y).unwrap());
    }



}

fn prove_example2() {
    println!("prove_example2");

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x = Int::new_const(&ctx,"x");
    let y = Int::new_const(&ctx,"y");
    let z = Int::new_const(&ctx,"z");
    let int_sort = Sort::int(&ctx);

    let g = FuncDecl::new(&ctx, "g", &[&int_sort], &int_sort);

    let g_of_x = g.apply(&[&Dynamic::from(x.clone())]);
    let g_of_y = g.apply(&[&Dynamic::from(y.clone())]);
    let g_of_z = g.apply(&[&Dynamic::from(z.clone())]);
    let g_of_x_min_g_of_y = Int::sub(&ctx, &[&g_of_x.as_int().unwrap(), &g_of_y.as_int().unwrap()]);
    let g_of_minus = g.apply(&[&Dynamic::from(g_of_x_min_g_of_y.clone())]);
    let equality_of_gs = Int::_eq(&g_of_minus.as_int().unwrap(), &g_of_z.as_int().unwrap()).not();
    let x_add_z = Int::add(&ctx, &[&x, &z]);
    let x_add_z_le_y = x_add_z.le(&y);
    let y_le_x = y.le(&x);
    let and_all = Bool::and(&ctx, &[&equality_of_gs, &x_add_z_le_y, &y_le_x]);




    let conjecture1 = Bool::implies(
            &and_all,
         &z.lt(&Int::from_i64(&ctx, 0))
    );

    let solver = Solver::new(&ctx);

    solver.assert(&conjecture1.not());
    println!("\nConjecture 1:\n{}\n", conjecture1);


    if solver.check() == SatResult::Unsat {
        println!("(g(g(x) - g(y)) != g(z) && x + z <= y && y <= x) -> z < 0 is Proved");
    } else {
        println!("(g(g(x) - g(y)) != g(z) && x + z <= y && y <= x) -> z < 0 is Failed to Prove");
    }

    let conjecture2 = Bool::implies(
        &and_all,
        &z.lt(&Int::from_i64(&ctx, -1))
    );

    solver.reset();
    solver.assert(&conjecture2.not());
    println!("\nConjecture 2:\n{}\n", conjecture2);

    if solver.check() == SatResult::Unsat {
        println!("(g(g(x) - g(y)) != g(z) && x + z <= y && y <= x) -> z < -1 is Proved");
    } else {
        println!("(g(g(x) - g(y)) != g(z) && x + z <= y && y <= x) -> z < -1 is Failed to Prove");
        println!("Counter Example:");
        println!("{}", solver.get_model().unwrap());
    }

}