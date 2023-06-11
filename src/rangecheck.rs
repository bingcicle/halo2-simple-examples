use std::marker::PhantomData;

use halo2_proofs::{arithmetic::*, circuit::*, plonk::*, poly::Rotation};

#[derive(Debug, Clone)]
struct RangeCheckConfig<F: FieldExt, const RANGE: usize> {
    value: Column<Advice>,
    q_range_check: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const RANGE: usize> RangeCheckConfig<F, RANGE> {
    fn configure(meta: &mut ConstraintSystem<F>, value: Column<Advice>) -> Self {
        // Toggle range check constraint
        let q_range_check = meta.selector();

        let config = Self {
            q_range_check,
            value,
            _marker: PhantomData,
        };

        meta.create_gate("Range check", |meta| {
            let q_range_check = meta.query_selector(q_range_check);
            let value = meta.query_advice(value, Rotation::cur());

            let range_check = |range, value: Expression<F>| {
                (0..range).fold(value.clone(), |expr, i| {
                    expr * (Expression::Constant(F::from(i as u64)) - value.clone())
                })
            };

            Constraints::with_selector(q_range_check, [("range check", range_check(8, value))])
        });
        config
    }

    fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "Assign value",
            |mut region| {
                let offset = 0;
                self.q_range_check.enable(&mut region, 0)?;

                region.assign_advice(|| "assign value", self.value, offset, || value)?;

                Ok(())
            },
        )
    }
}
pub fn rangecheck(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{circuit::floor_planner::V1, dev::*, pasta::Fp};

    use super::*;

    #[derive(Default)]
    struct TestCircuit<F: FieldExt, const RANGE: usize> {
        value: Value<Assigned<F>>,
    }

    impl<F: FieldExt, const RANGE: usize> Circuit<F> for TestCircuit<F, RANGE> {
        type Config = RangeCheckConfig<F, RANGE>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            RangeCheckConfig::configure(meta, value)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.assign(layouter.namespace(|| "Assign value"), self.value)?;

            Ok(())
        }
    }

    #[test]
    fn test_rangecheck() {
        let k = 4;
        const RANGE: usize = 8;

        for i in 0..RANGE {
            let passing_circuit = TestCircuit::<Fp, RANGE> {
                value: Value::known(Fp::from(i as u64).into()),
            };

            let prover = MockProver::run(k, &passing_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        let failing_circuit = TestCircuit::<Fp, RANGE> {
            value: Value::known(Fp::from((RANGE) as u64).into()),
        };

        let prover = MockProver::run(k, &failing_circuit, vec![]).unwrap();
        assert_eq!(
            prover.verify(),
            Err(vec![VerifyFailure::ConstraintNotSatisfied {
                constraint: ((0, "Range check").into(), 0, "range check").into(),
                location: FailureLocation::InRegion {
                    region: (0, "Assign value").into(),
                    offset: 0
                },
                cell_values: vec![(((Any::Advice, 0).into(), 0).into(), "0x8".to_string())]
            }])
        );
    }
}
