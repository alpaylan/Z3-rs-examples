use z3::{ast::{
    Bool,
    Ast,
    Int,
    Dynamic,
}, Context, Config, SatResult, FuncDecl, Sort, Solver};
use z3::ast::BV;
use std::ops::Add;
use std::borrow::Borrow;


pub trait BoolEx<'ctx> {
    fn _and(&self , other: &'ctx Bool) -> Bool<'ctx>;
    fn _or(&self,  other: &'ctx Bool) -> Bool<'ctx>;
    fn as_dynamic(&self) -> Dynamic<'ctx>;
}

impl<'ctx> BoolEx<'ctx> for Bool<'ctx> {
    fn _and(&self , other: &'ctx Bool) -> Bool<'ctx> {
        Bool::and(&self.get_ctx(), &[&self, &other])
    }
    fn _or(&self, other: &'ctx Bool) -> Bool<'ctx> {
        Bool::or(&self.get_ctx(), &[&self, &other])
    }
    fn as_dynamic(&self) -> Dynamic<'ctx> {
        Dynamic::from(self.clone())
    }
}

pub trait IntEx<'ctx> {
    fn _add(&self , other: &'ctx Int) -> Int<'ctx>;
    fn _sub(&self,  other: &'ctx Int) -> Int<'ctx>;
    fn _mul(&self,  other: &'ctx Int) -> Int<'ctx>;
    fn as_dynamic(&self) -> Dynamic<'ctx>;
}

impl<'ctx> IntEx<'ctx> for Int<'ctx> {
    fn _add(&self , other: &'ctx Int) -> Int<'ctx> {
        Int::add(&self.get_ctx(), &[&self, &other])
    }
    fn _sub(&self, other: &'ctx Int) -> Int<'ctx> {
        Int::sub(&self.get_ctx(), &[&self, &other])
    }
    fn _mul(&self, other: &'ctx Int) -> Int<'ctx> {
        Int::mul(&self.get_ctx(), &[&self, &other])
    }
    fn as_dynamic(&self) -> Dynamic<'ctx> {
        Dynamic::from(self.clone())
    }
}


fn main() {
    // de_morgan();
    // prove_example1();
    // prove_example2();
    // fpe();
    // ite_example();
    sudoku_example();
}


fn de_morgan() {
    println!("De Morgan Example");
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let x1 = Bool::new_const(&ctx, "x1");
    let x2 = Bool::new_const(&ctx, "x2");
    let x3 = &x2._and(&x1);
    let x4 = &x3.not();
    let x5 = &x1.not();
    let x6 = &x2.not();
    let x7 = &x5._or(&x6);
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
            &Int::_eq(&x, &y),
            &Int::_eq(
                &(g.apply(&[&x.as_dynamic()]).as_int()).unwrap(),
                &(g.apply(&[&y.as_dynamic()]).as_int()).unwrap()
            )
        );

    solver.assert(&conjecture1.not());


    if solver.check() == SatResult::Unsat {
        println!("x == y -> g(x) == g(y) Proved\n");
    } else {
        println!("x == y -> g(x) == g(y) Failed to Prove\n");
    }

    solver.reset();

    let g_of_g_of_x = g.apply(&[&g.apply(&[ &x.as_dynamic()])]).as_int().unwrap();
    let g_of_y = g.apply(&[&y.as_dynamic()]).as_int().unwrap();

    let conjecture2 = Bool::implies(
        &x._eq(&y),
        &Int::_eq(&g_of_g_of_x, &g_of_y)
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

    let g_of_x = g.apply(&[&x.as_dynamic()]);
    let g_of_y = g.apply(&[&y.as_dynamic()]);
    let g_of_z = g.apply(&[&z.as_dynamic()]);
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

fn fpe() {
    println!("fpe_example");

    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);

    let a0 = BV::new_const(&ctx,"a0", 32);        // int a0 = atoi(argv[1]);
    let a1 = BV::new_const(&ctx,"a1", 32);        // int a1 = atoi(argv[2]);


    /*
     int f(int b) {
         return b + 5;
     }
     */

    let bv_s = Sort::bitvector(&ctx, 32);
    let f = FuncDecl::new(&ctx,"f", &[&bv_s], &bv_s);
    let b = BV::new_const(&ctx,"b", 32);
    let t0 = BV::from_i64(&ctx, 5, 32);
    let t1 = b.bvadd(&t0);
    let t2 = f.apply(&[&Dynamic::from( (&b).clone())]);
    let t3 = t1._eq(&t2.as_bv().unwrap());

    solver.assert(&t3);
    solver.assert(&a0._eq(&BV::from_i64(&ctx, 1, 32)));
    solver.assert(&a1._eq(&BV::from_i64(&ctx, -5, 32)));
    let c = f.apply(&[&Dynamic::from( (&a1).clone())]);

    let a_over_c = a0.bvsdiv(&c.as_bv().unwrap());

    solver.assert(&a_over_c._eq(&BV::from_i64(&ctx, 1, 32)));
    println!("{}", solver.check() == SatResult::Unsat);
    let model = solver.get_model().unwrap();
    println!("{}", model);
}

fn ite_example() {
    println!("if-then-else example");
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let f = Bool::from_bool(&ctx, true);
    let one = Int::from_i64(&ctx, 1);
    let zero = Int::from_i64(&ctx, 0);
    let ite  = f.ite(&one, &zero);

    println!("{}", ite.simplify());
}

fn sudoku_example() {
    println!("sudoku_example");
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let solver = Solver::new(&ctx);
    let mut arena : Vec<Vec<z3::ast::Int>> = Vec::with_capacity(9);

    for i in 0..9 {
        arena.push(Vec::with_capacity(9));
        for j in 0..9 {
            arena[i].push( Int::new_const(&ctx,String::add("c_".parse().unwrap(), &*String::add((&*i.to_string()).parse().unwrap(), &*j.to_string()))));
        }
    }

    for i in 0..9 {
        for j in 0..9 {
            solver.assert(arena[i][j].ge(&Int::from_i64(&ctx, 1)).borrow());
            solver.assert(arena[i][j].le(&Int::from_i64(&ctx, 9)).borrow());
        }
    }

    for i in 0..9 {
        let mut row = Vec::new();
        for j in 0..9 {
            row.push(arena[i][j].borrow());
        }
        solver.assert(Ast::distinct(&ctx, row.borrow()).borrow());
    }

    for i in 0..9 {
        let mut col = Vec::new();
        for j in 0..9 {
            col.push(arena[j][i].borrow());
        }
        solver.assert(Ast::distinct(&ctx, col.borrow()).borrow());
    }

    for i in 0..3 {
        for j in 0..3 {
            let mut sub_arena = Vec::new();
            for sub_i in 0..3 {
                for sub_j in 0..3 {
                    sub_arena.push(arena[i*3 + sub_i][j*3 + sub_j].borrow());
                }
            }
            solver.assert(Ast::distinct(&ctx, sub_arena.borrow()).borrow());
        }
    }
    // sudoku instance, we use '0' for empty cells
    let instance =
        [
            [0, 0, 0, 0, 9, 4, 0, 3, 0],
            [0, 0, 0, 5, 1, 0, 0, 0, 7],
            [0, 8, 9, 0, 0, 0, 0, 4, 0],
            [0, 0, 0, 0, 0, 0, 2, 0, 8],
            [0, 6, 0, 2, 0, 1, 0, 5, 0],
            [1, 0, 2, 0, 0, 0, 0, 0, 0],
            [0, 7, 0, 0, 0, 0, 5, 2, 0],
            [9, 0, 0, 0, 6, 5, 0, 0, 0],
            [0, 4, 0, 9, 7, 0, 0, 0, 0]
        ];

    for i in 0..9 {
        for j in 0..9 {
            if instance[i][j] != 0 {
                solver.assert(arena[i][j]._eq(Int::from_i64(&ctx, instance[i][j]).borrow()).borrow());
            }
        }
    }

    println!("{}", solver.check() == SatResult::Sat);
    println!("{}", solver);

    let model = solver.get_model().unwrap();
    for i in 0..9 {
        for j in 0..9 {
            print!("{}", model.eval(arena[i][j].borrow()).unwrap());
            if j % 3 == 2 {
                print!(" ")
            }
        }
        println!("");
        if i % 3 == 2 {
            println!("")
        }
    }
}