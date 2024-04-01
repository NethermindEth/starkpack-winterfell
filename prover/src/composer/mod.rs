// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use super::{constraints::CompositionPoly, StarkDomain, TracePolyTable};
use air::DeepCompositionCoefficients;
use math::{add_in_place, fft, mul_acc, polynom, ExtensionOf, FieldElement, StarkField};
use utils::{collections::Vec, iter_mut};

#[cfg(feature = "concurrent")]
use utils::iterators::*;

// DEEP COMPOSITION POLYNOMIAL
// ================================================================================================
pub struct DeepCompositionPoly<E: FieldElement> {
    coefficients: Vec<E>,
    cc: DeepCompositionCoefficients<E>,
    z: E,
}

impl<E: FieldElement> DeepCompositionPoly<E> {
    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    /// Returns a new DEEP composition polynomial. Initially, this polynomial will be empty, and
    /// the intent is to populate the coefficients via add_trace_polys() and add_constraint_polys()
    /// methods.
    pub fn new(z: E, cc: DeepCompositionCoefficients<E>) -> Self {
        DeepCompositionPoly {
            coefficients: vec![],
            cc,
            z,
        }
    }

    // ACCESSORS
    // --------------------------------------------------------------------------------------------

    /// Returns the size of the DEEP composition polynomial.
    pub fn poly_size(&self) -> usize {
        self.coefficients.len()
    }

    /// Returns the degree of the composition polynomial.
    pub fn degree(&self) -> usize {
        polynom::degree_of(&self.coefficients)
    }

    // TRACE POLYNOMIAL COMPOSITION
    // --------------------------------------------------------------------------------------------
    /// Combines all traces polynomials into a single polynomial and saves the result into
    /// the DEEP composition polynomial. The combination is done as follows:
    ///
    /// - Compute polynomials T'_i(x) = (T_i(x) - T_i(z)) / (x - z) and
    ///   T''_i(x) = (T_i(x) - T_i(z * g)) / (x - z * g) for all i, where T_i(x) is a trace
    ///   polynomial for column i.
    /// - Then, combine together all T'_i(x) and T''_i(x) polynomials using a random linear
    ///   combination as T(x) = sum((T'_i(x) + T''_i(x)) * cc_i) for all i, where cc_i is
    ///   the coefficient for the random linear combination drawn from the public coin.
    /// - Repeat this 2 steps for all the trace_polys.
    /// - Combine all the polys into one.
    /// Note that evaluations of T_i(z) and T_i(z * g) are passed in via the `ood_trace_state`
    /// parameter.
    pub fn add_trace_polys(
        &mut self,
        traces_polys: Vec<TracePolyTable<E>>,
        ood_traces_states: Vec<Vec<Vec<E>>>,
    ) {
        //TODO check this for the first one?
        //assert!(self.coefficients.is_empty());
        let mut trace_poly_vec = Vec::new();
        for (index, trace_polys) in traces_polys.iter().enumerate() {
            // compute a second out-of-domain point offset from z by exactly trace generator; this
            // point defines the "next" computation state in relation to point z
            let trace_length = trace_polys.poly_size();
            let g = E::from(E::BaseField::get_root_of_unity(trace_length.ilog2()));
            let next_z = self.z * g;
            // combine trace polynomials into 2 composition polynomials T'(x) and T''(x)
            let mut t1_composition = E::zeroed_vector(trace_length);
            let mut t2_composition = E::zeroed_vector(trace_length);

            // index of a trace polynomial; we declare it here so that we can maintain index continuity
            // across all trace segments
            let mut i = 0;

            // --- merge polynomials of the main trace segment ----------------------------------------
            for poly in trace_polys.main_trace_polys() {
                // compute T'(x) = T(x) - T(z), multiply it by a pseudo-random coefficient,
                // and add the result into composition polynomial
                acc_trace_poly::<E::BaseField, E>(
                    &mut t1_composition,
                    poly,
                    ood_traces_states[index][0][i],
                    self.cc.traces[index][i],
                );

                // compute T''(x) = T(x) - T(z * g), multiply it by a pseudo-random coefficient,
                // and add the result into composition polynomial
                acc_trace_poly::<E::BaseField, E>(
                    &mut t2_composition,
                    poly,
                    ood_traces_states[index][1][i],
                    self.cc.traces[index][i],
                );

                i += 1;
            }
            // --- merge polynomials of the auxiliary trace segments ----------------------------------
            for poly in trace_polys.aux_trace_polys() {
                // compute T'(x) = T(x) - T(z), multiply it by a pseudo-random coefficient,
                // and add the result into composition polynomial
                acc_trace_poly::<E, E>(
                    &mut t1_composition,
                    poly,
                    ood_traces_states[index][0][i],
                    self.cc.traces[index][i],
                );

                // compute T''(x) = T(x) - T(z * g), multiply it by a pseudo-random coefficient,
                // and add the result into composition polynomial
                acc_trace_poly::<E, E>(
                    &mut t2_composition,
                    poly,
                    ood_traces_states[index][1][i],
                    self.cc.traces[index][i],
                );

                i += 1;
            }
            // divide the composition polynomials by (x - z) and (x - z * g), respectively,
            // and add the resulting polynomials together; the output of this step
            // is a single trace polynomial T(x) and deg(T(x)) = trace_length - 2.
            let trace_poly = merge_trace_compositions(
                vec![t1_composition, t2_composition],
                vec![self.z, next_z],
            );
            trace_poly_vec.push(trace_poly);
        }
        //Combine all the trace polys into one final polynomial.
        let first_poly = trace_poly_vec.first().unwrap().to_owned();
        let rem_polys: Vec<_> = trace_poly_vec.iter().skip(1).collect();
        let final_trace_poly = rem_polys
            .into_iter()
            .fold(first_poly, |mut acc, next_poly| {
                add_in_place(&mut acc, next_poly);
                acc
            });
        // set the coefficients of the DEEP composition polynomial
        self.coefficients = final_trace_poly;
        // TODO^ Check again here
        assert_eq!(self.poly_size() - 2, self.degree());
    }

    // CONSTRAINT POLYNOMIAL COMPOSITION
    // --------------------------------------------------------------------------------------------
    /// Divides out OOD point z from the constraint composition polynomial and saves the result
    /// into the DEEP composition polynomial. This method is intended to be called only after the
    /// add_trace_polys() method has been executed. The composition is done as follows:
    ///
    /// - For each H_i(x), compute H'_i(x) = (H_i(x) - H(z)) / (x - z), where H_i(x) is the
    ///   ith composition polynomial column.
    /// - Then, combine all H_i(x) polynomials together by computing H(x) = sum(H_i(x) * cc_i) for
    ///   all i, where cc_i is the coefficient for the random linear combination drawn from the
    ///   public coin.
    ///
    /// Note that evaluations of H_i(x) at z are passed in via the `ood_evaluations` parameter.
    pub fn add_composition_poly(
        &mut self,
        composition_poly: CompositionPoly<E>,
        ood_evaluations: Vec<E>,
    ) {
        assert!(!self.coefficients.is_empty());

        let z = self.z;

        let mut column_polys = composition_poly.into_columns();

        // Divide out the OOD point z from column polynomials
        iter_mut!(column_polys)
            .zip(ood_evaluations)
            .for_each(|(poly, value_at_z)| {
                // compute H'_i(x) = (H_i(x) - H_i(z)) / (x - z)
                poly[0] -= value_at_z;
                polynom::syn_div_in_place(poly, 1, z);
            });

        // add H'_i(x) * cc_i for all i into the DEEP composition polynomial
        for (i, poly) in column_polys.into_iter().enumerate() {
            mul_acc::<E, E>(&mut self.coefficients, &poly, self.cc.constraints[i]);
        }
        assert_eq!(self.poly_size() - 2, self.degree());
    }

    // LOW-DEGREE EXTENSION
    // --------------------------------------------------------------------------------------------
    /// Evaluates DEEP composition polynomial over the specified LDE domain and returns the result.
    pub fn evaluate(self, domain: &StarkDomain<E::BaseField>) -> Vec<E> {
        fft::evaluate_poly_with_offset(
            &self.coefficients,
            domain.trace_twiddles(),
            domain.offset(),
            domain.trace_to_lde_blowup(),
        )
    }
}

// HELPER FUNCTIONS
// ================================================================================================

/// Divides each polynomial in the list by the corresponding divisor, and computes the
/// coefficient-wise sum of all resulting polynomials.
fn merge_trace_compositions<E: FieldElement>(mut polys: Vec<Vec<E>>, divisors: Vec<E>) -> Vec<E> {
    // divide all polynomials by their corresponding divisor
    iter_mut!(polys).zip(divisors).for_each(|(poly, divisor)| {
        polynom::syn_div_in_place(poly, 1, divisor);
    });

    // add all polynomials together into a single polynomial
    let mut result = polys.remove(0);
    for poly in polys.iter() {
        add_in_place(&mut result, poly);
    }

    result
}

/// Computes (P(x) - value) * k and saves the result into the accumulator.
fn acc_trace_poly<F, E>(accumulator: &mut [E], poly: &[F], value: E, k: E)
where
    F: FieldElement,
    E: FieldElement<BaseField = F::BaseField> + ExtensionOf<F>,
{
    mul_acc(accumulator, poly, k);
    let adjusted_tz = value * k;
    accumulator[0] -= adjusted_tz;
}
