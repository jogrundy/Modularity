//
//  matrix_utilities.h
//  expt1
//
//  Created by Joanna Houghton on 10/08/2018.
//  Copyright © 2018 JoSoft. All rights reserved.
//

#ifndef matrix_utilities_h
#define matrix_utilities_h

#include <stdio.h>
#include <Accelerate/Accelerate.h>

int make_adj_mat(double *arr, int *adj_mat, const int size, double eps, int N, bool directed);
void matrix_transpose_i(int *mat_src, int *mat_dest, int N);
void matrix_transpose_d(double *mat_src, double * mat_dest, int N);
void matrix_add(double *mat_src, double *mat_dest, int N);
double sparse_get_element_double(sparse_matrix_double A, unsigned i, unsigned j, int ind);
void sparse_identity_matrix(sparse_matrix_double *A, int N);
void load_matrix(double *matrix, const int size, char *filename);
void test_matrix_utilities(void);
void print_double_matrix(double *matrix, int n_rows, int n_cols);
void print_int_matrix(int *matrix, int n_rows, int n_cols);
int make_double_adj_mat(double *arr, double *adj_mat, const int size, double eps, int N, bool directed);
#endif /* matrix_utilities_h */
