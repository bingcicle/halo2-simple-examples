use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, dev::MockProver, pasta::Fp, plonk::*, poly::Rotation,
};

#[derive(Clone, Copy)]
struct FiboConfig {
    pub advice: [Column<Advice>; 3],
    pub selector: Selector,
}

struct FiboChip<F: FieldExt> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct ACell<F: FieldExt>(AssignedCell<F, F>);

impl<F: FieldExt> FiboChip<F> {
    fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> FiboConfig {
        let col_a: Column<Advice> = meta.advice_column();
        let col_b: Column<Advice> = meta.advice_column();
        let col_c: Column<Advice> = meta.advice_column();
        let selector: Selector = meta.selector();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);

        meta.create_gate("add", |meta| {
            // Custom gate layout looks like:
            // col_a | col_b | col_c | selector
            // ---------------------------------
            //  a    |   b   |   c   |   s
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            // This is our constraint: s (selector) can be turned on/off.
            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice: [col_a, col_b, col_c],
            selector,
        }
    }

    fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: Option<F>,
        b: Option<F>,
    ) -> Result<(ACell<F>, ACell<F>, ACell<F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let a_val = a.ok_or(Error::Synthesis).map(Value::known)?;
                let b_val = b.ok_or(Error::Synthesis).map(Value::known)?;

                let a_cell = region
                    .assign_advice(|| "a", self.config.advice[0], 0, || a_val)
                    .map(ACell)?;
                let b_cell = region
                    .assign_advice(|| "b", self.config.advice[1], 0, || b_val)
                    .map(ACell)?;

                let c_val = a
                    // To test if our constraint satisfiability works as intended, we can change
                    // what's inside here to:
                    // .and_then(|a| b.map(|b| a + b + b))
                    //
                    // A nice error message is printed out, with:
                    //   Constraint '':
                    //   S0 * (x0 + x1 - x2) = 0
                    // This tells you that the above equation does not hold and thus our
                    // constraint is not satisfied.
                    .and_then(|a| b.map(|b| a + b))
                    .ok_or(Error::Synthesis)
                    .map(Value::known)?;

                let c_cell = region
                    .assign_advice(|| "c", self.config.advice[2], 0, || c_val)
                    .map(ACell)?;
                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        prev_b: &ACell<F>,
        prev_c: &ACell<F>,
    ) -> Result<ACell<F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                prev_b
                    .0
                    .copy_advice(|| "a", &mut region, self.config.advice[0], 0)?;
                prev_c
                    .0
                    .copy_advice(|| "b", &mut region, self.config.advice[1], 0)?;

                let c_val = prev_b
                    .0
                    .value()
                    .and_then(|b| prev_c.0.value().map(|c| *b + *c));

                let c_cell = region
                    .assign_advice(|| "c", self.config.advice[2], 0, || c_val)
                    .map(ACell)?;
                Ok(c_cell)
            },
        )
    }
}

#[derive(Default)]
struct MyCircuit<F> {
    pub a: Option<F>,
    pub b: Option<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FiboConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FiboChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FiboChip::construct(config);

        let (_, mut prev_b, mut prev_c) =
            chip.assign_first_row(layouter.namespace(|| "first row"), self.a, self.b)?;

        // Prove f(9) == z
        for _ in 3..10 {
            let c = chip.assign_row(layouter.namespace(|| "next row"), &prev_b, &prev_c)?;

            prev_b = prev_c;
            prev_c = c;
        }

        Ok(())
    }
}

pub fn fibonacci_simple(k: u32) -> Result<MockProver<Fp>, Error> {
    let a = Fp::from(1);
    let b = Fp::from(1);

    let circuit = MyCircuit {
        a: Some(a),
        b: Some(b),
    };

    MockProver::run(k, &circuit, vec![])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fibonacci() {
        let result = fibonacci_simple(4).unwrap();
        result.assert_satisfied()
    }
}
