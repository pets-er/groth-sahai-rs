//! Contains the functionality for verifying the satisfiability of Groth-Sahai equations over bilinear groups.
//!
//! Verifying an equation's proof primarily involves addition in [`BT`](crate::data_structures::ComT) (equiv. multiplication in 4 [`GT`](ark_ec::PairingEngine::Fqk))
//! and pairings over elements in [`B1`](crate::data_structures::Com1) and [`B2`](crate::data_structures::Com2).
//!
//! See the [`prover`](crate::prover) and [`statement`](crate::statement) modules for more details about the structure of the equations and their proofs.

use ark_ec::PairingEngine;

use crate::data_structures::*;
use crate::generator::*;
use crate::prover::CProof;
use crate::statement::*;

/// A collection of attributes containing verifier functionality for an [`Equation`](crate::statement::Equation).
pub trait Verifiable<E: PairingEngine> {

    /// Verifies that a single Groth-Sahai equation is satisfied using the prover's committed `x` and `y` variables.
    fn verify(&self, com_proof: &CProof<E>, crs: &CRS<E>) -> bool;
}

impl<E: PairingEngine> Verifiable<E> for PPE<E> {

    fn verify(&self, com_proof: &CProof<E>, crs: &CRS<E>) -> bool {

        assert_eq!(com_proof.equ_proofs.len(), 1);
        assert_eq!(self.get_type(), com_proof.equ_proofs[0].equ_type);
        let is_parallel = true;

        let lin_a_com_y = ComT::<E>::pairing_sum(&Com1::<E>::batch_linear_map(&self.a_consts), &com_proof.ycoms.coms);

        let com_x_lin_b = ComT::<E>::pairing_sum(&com_proof.xcoms.coms, &Com2::<E>::batch_linear_map(&self.b_consts));

        let stmt_com_y: Matrix<Com2<E>> = vec_to_col_vec(&com_proof.ycoms.coms).left_mul(&self.gamma, is_parallel);
        let com_x_stmt_com_y = ComT::<E>::pairing_sum(&com_proof.xcoms.coms, &col_vec_to_vec(&stmt_com_y));

        let lin_t = ComT::<E>::linear_map_PPE(&self.target);

        let com1_pf2 = ComT::<E>::pairing_sum(&crs.u, &com_proof.equ_proofs[0].pi);

        let pf1_com2 = ComT::<E>::pairing_sum(&com_proof.equ_proofs[0].theta, &crs.v);

        let lhs: ComT<E> = lin_a_com_y + com_x_lin_b + com_x_stmt_com_y;
        let rhs: ComT<E> = lin_t + com1_pf2 + pf1_com2;

        lhs == rhs
    }
}

impl<E: PairingEngine> Verifiable<E> for MSMEG1<E> {

    fn verify(&self, com_proof: &CProof<E>, crs: &CRS<E>) -> bool {

        assert_eq!(com_proof.equ_proofs.len(), 1);
        assert_eq!(self.get_type(), com_proof.equ_proofs[0].equ_type);
        let is_parallel = true;

        let lin_a_com_y = ComT::<E>::pairing_sum(&Com1::<E>::batch_linear_map(&self.a_consts), &com_proof.ycoms.coms);

        let com_x_lin_b = ComT::<E>::pairing_sum(&com_proof.xcoms.coms, &Com2::<E>::batch_scalar_linear_map(&self.b_consts, &crs));

        let stmt_com_y: Matrix<Com2<E>> = vec_to_col_vec(&com_proof.ycoms.coms).left_mul(&self.gamma, is_parallel);
        let com_x_stmt_com_y = ComT::<E>::pairing_sum(&com_proof.xcoms.coms, &col_vec_to_vec(&stmt_com_y));

        let lin_t = ComT::<E>::linear_map_MSMEG1(&self.target, &crs);

        let com1_pf2 = ComT::<E>::pairing_sum(&crs.u, &com_proof.equ_proofs[0].pi);

        let pf1_com2 = ComT::<E>::pairing(com_proof.equ_proofs[0].theta[0].clone(), crs.v[0].clone());

        let lhs: ComT<E> = lin_a_com_y + com_x_lin_b + com_x_stmt_com_y;
        let rhs: ComT<E> = lin_t + com1_pf2 + pf1_com2;

        lhs == rhs
    }
}

impl<E: PairingEngine> Verifiable<E> for MSMEG2<E> {

    fn verify(&self, com_proof: &CProof<E>, crs: &CRS<E>) -> bool {

        assert_eq!(com_proof.equ_proofs.len(), 1);
        assert_eq!(self.get_type(), com_proof.equ_proofs[0].equ_type);
        let is_parallel = true;

        let lin_a_com_y = ComT::<E>::pairing_sum(&Com1::<E>::batch_scalar_linear_map(&self.a_consts, &crs), &com_proof.ycoms.coms);

        let com_x_lin_b = ComT::<E>::pairing_sum(&com_proof.xcoms.coms, &Com2::<E>::batch_linear_map(&self.b_consts));

        let stmt_com_y: Matrix<Com2<E>> = vec_to_col_vec(&com_proof.ycoms.coms).left_mul(&self.gamma, is_parallel);
        let com_x_stmt_com_y = ComT::<E>::pairing_sum(&com_proof.xcoms.coms, &col_vec_to_vec(&stmt_com_y));

        let lin_t = ComT::<E>::linear_map_MSMEG2(&self.target, &crs);

        let com1_pf2 = ComT::<E>::pairing(crs.u[0].clone(), com_proof.equ_proofs[0].pi[0].clone());

        let pf1_com2 = ComT::<E>::pairing_sum(&com_proof.equ_proofs[0].theta, &crs.v);

        let lhs: ComT<E> = lin_a_com_y + com_x_lin_b + com_x_stmt_com_y;
        let rhs: ComT<E> = lin_t + com1_pf2 + pf1_com2;

        lhs == rhs
    }
}

impl<E: PairingEngine> Verifiable<E> for QuadEqu<E> {

    fn verify(&self, com_proof: &CProof<E>, crs: &CRS<E>) -> bool {

        assert_eq!(com_proof.equ_proofs.len(), 1);
        assert_eq!(self.get_type(), com_proof.equ_proofs[0].equ_type);
        let is_parallel = true;

        let lin_a_com_y = ComT::<E>::pairing_sum(&Com1::<E>::batch_scalar_linear_map(&self.a_consts, &crs), &com_proof.ycoms.coms);

        let com_x_lin_b = ComT::<E>::pairing_sum(&com_proof.xcoms.coms, &Com2::<E>::batch_scalar_linear_map(&self.b_consts, &crs));

        let stmt_com_y: Matrix<Com2<E>> = vec_to_col_vec(&com_proof.ycoms.coms).left_mul(&self.gamma, is_parallel);
        let com_x_stmt_com_y = ComT::<E>::pairing_sum(&com_proof.xcoms.coms, &col_vec_to_vec(&stmt_com_y));

        let lin_t = ComT::<E>::linear_map_quad(&self.target, &crs);

        let com1_pf2 = ComT::<E>::pairing(crs.u[0].clone(), com_proof.equ_proofs[0].pi[0].clone());

        let pf1_com2 = ComT::<E>::pairing(com_proof.equ_proofs[0].theta[0].clone(), crs.v[0].clone());

        let lhs: ComT<E> = lin_a_com_y + com_x_lin_b + com_x_stmt_com_y;
        let rhs: ComT<E> = lin_t + com1_pf2 + pf1_com2;

        lhs == rhs
    }
}
// TODO adjust to verifiable 
fn batched_verify(pp: &HashMap<String, ElementType>, crs: &HashMap<String, Vec<ElementType>>, 
                  proof: &Vec<HashMap<String, Vec<ElementType>>>, com_x: &Vec<Vec<ElementType>>, 
                  com_y: &Vec<Vec<ElementType>>, gamma_t: &Vec<ElementType>) -> bool {
    // Initialize dictionaries and LHS
    let mut p1: HashMap<usize, ElementType> = HashMap::new();
    let mut p2: HashMap<usize, ElementType> = HashMap::new();
    let mut lhs: ElementType = Element::one();
    
    // Set m to the length of com_x and n to the length of com_y
    let m = com_x.len();
    let n = com_y.len();
    
    let mut p1_values: Vec<ElementType> = Vec::with_capacity(m + 4);
    let mut p2_values: Vec<ElementType> = Vec::with_capacity(m + 4);
    
    let mut s: Vec<ElementType> = vec![Group::random(), Group::random()];
    let mut r: Vec<ElementType> = vec![Group::random(), Group::random()];
    
    // Loop over all possible combinations of vv1 and vv2
    for ii in 0..gamma_t.len() {
        let gamma_t_value = gamma_t[ii];
        let pi = &proof[ii];
        
        for vv1 in [0, 1].iter() {
            for vv2 in [0, 1].iter() {
                for i in 0..m {
                    p1.insert(i, com_x[i][*vv1]);
                    p2.insert(i, Element::one());
                    for j in 0..n {
                        p2.entry(i).and_modify(|entry| *entry *= com_y[j][*vv2].pow(gamma_t_value[j][i]));
                    }
                }
            }
        }
        
        p1_values = (0..m + 4).map(|i| {
            match i {
                m => crs["vv1"][vv1].inverse().unwrap(),
                m + 1 => crs["ww1"][vv1].inverse().unwrap(),
                m + 2 => pi["pi_v2"][vv1],
                m + 3 => pi["pi_w2"][vv1],
                _ => p1[&i],
            }
        }).collect();
        
        p2_values = (0..m + 4).map(|i| {
            match i {
                m => pi["pi_v1"][vv1],
                m + 1 => pi["pi_w1"][vv1],
                m + 2 => crs["vv2"][vv1].inverse().unwrap(),
                m + 3 => crs["ww2"][vv1].inverse().unwrap(),
                _ => p2[&i],
            }
        }).collect();
        
        // Compute the pairing of each element in p1_values and p2_values, and multiply them all and keep them in lhs
        for k in 0..m + 4 {
            let pairing_result = pair(p1_values[k].pow(s[0]) * p1_values[k].pow(s[1]), p2_values[k].pow(r[0]) * p2_values[k].pow(r[1]));
            lhs *= pairing_result;
        }
    }
    
    // Check if lhs is equal to the identity value in GT, i.e. pp["GT"]^0, and return the result
    lhs == pp["GT"].pow(&[Element::zero()])
}
/*
 * NOTE:
 *
 * Proof verification tests are considered integration tests for the Groth-Sahai proof system.
 *
 *
 * See tests/prover.rs for more details.
 */
