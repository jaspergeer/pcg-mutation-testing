fn use_of_moved_value<T>(x: T) {
    let y = x;
    // x;
}

fn cannot_be_used_because_it_is_borrowed() {
    let mut x = 1;
    let y = &mut x;
    // x = 2;
    // x;
    *y = 1;
}

fn cannot_borrow_as_mutable_more_than_once() {
    let mut x = 1;
    let x_ref_0 = &mut x;
    // let x_ref_1 = &mut x;
    *x_ref_0 = 1;
}

fn cannot_borrow_as_immutable_because_mutably_lent() {
    let mut x = 1;
    let x_ref_0 = &mut x;
    // let x_ref_1 = &x;
    *x_ref_0 = 1;
}

fn cannot_borrow_as_mutable_because_immutable() {
    let mut x = 1;
    let x_ref_0 = &x;
    // let x_ref_1 = &mut x;
    *x_ref_0;
}

fn immutable_borrows() {
    let x = 1;
    let y = &x;
    let z = &x;
    y + z;
}

fn use_of_partially_moved_value<T>(t: &mut T) {
    struct S<T>{f: T}
    let s = S { f: t };
    let _f_move = s.f;
    // s;
    // let _ = &mut s;
}

fn cannot_assign_to_shared(t: &i64) {
    // *t = 1;
}

fn cannot_move_out_of_ref<T>(x: &T, y: &mut T) {
    // *x;
    // *y;
}

fn lifetimes_fun() {
    fn lifetimes<'a, 'b : 'a, 'c : 'b, T>(x: &'a mut T, y: &'b T, z: &'c mut T) -> &'b mut T {
        z
    }
    let mut x = 1;
    let x_ref = &mut x;
    let mut y = 1;
    let y_ref = &mut y;
    let mut z = 1;
    let z_ref = &mut z;
    let a = lifetimes(x_ref, y_ref, z_ref);
    // *y_ref = 0;
    a;
}

// error message: cannot assign bc borrowed
fn abstraction_edge(x: &mut i64) {
    fn abstraction<'a>(t: &'a mut i64) -> &'a mut i64 {
        let y = &*t;
        let x = &t;
        return t;
    }
    let y = abstraction(x);
    // x;
    // let mut _ = &mut x;
    // let _ = &x;
    let _ = &y;
}

fn path_sensitive() {
    let mut a = 1;
    let mut b = 1;
    let mut f: &mut i64 = &mut a;
    let k: &mut i64 = &mut b;
    if true {
       f = &mut *k
    }
    // *k = 1;
    *f = 1;
    *k = 1;
}

fn alexs_knot() {
    struct S {
        f: i64,
        g: i64
    }
    let mut f = &mut 1;
    let mut k = &mut 1;
    // let mut f: &mut S = &mut S { f: 0, g: 0 };
    // let mut k: &mut S = &mut S { f: 0, g: 0 };
    if true {
        k = &mut *f;
        // k.f = 1;
        // f.f = 1;
    } else {
        f = &mut *k;
        // f.f = 1;
        // k.f = 1;
    }
    // f.f = 1;
    // k.f = 1;
}

fn cycle() {
    enum E<'a> {
        Empty(),
        Bar(),
        NonEmpty(&'a E<'a>)
    }
    let mut node_1 = E::Empty();
    let node_2 = E::NonEmpty(&node_1);
    let foo = Box::new(1);
    // node_1 = E::NonEmpty(&node_2);
    node_2;
}

fn main() {}
