//
//  matrix_utilities.c
//  expt1
//
//  Created by Joanna Houghton on 10/08/2018.
//  Copyright © 2018 JoSoft. All rights reserved.
//

#include "matrix_utilities.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <Accelerate/Accelerate.h>
#include "utilities.h"


int make_adj_mat(double *arr, int *adj_mat, const int size, double eps, int N, bool directed){
    //    takes the 1d array arr, prunes the lowest values less than eps, returns 1 for connection and 0 otherwise
    //    size is length of array, eps is the small amount above which we consider it a connection
    //    takes in adjacency matrix, gives out m
    //    adjacency matrix is 1 for connection, zero otherwise
    //        may be directed, ie unsymmetric
    //        number of edges = total off diag/2 + diags
    int i;
    float m=0; // m is number of edges
    if (directed){
        for (i=0;i<size;i++){
            if (fabs(arr[i]) > eps){ // if a connection
                adj_mat[i] = 1;
                m++;
            } else {
                adj_mat[i] = 0;
            }
        }
    } else {
        for (i=0;i<size;i++){
            if (fabs(arr[i]) > eps){ // if a connection
                adj_mat[i] = 1;
                int row = i/N;
                int col = i%N;
    //            m++;
                if (row==col){
                    m++;
                } else {
                    m+=0.5;
                }
            } else {
                adj_mat[i] = 0;
            }
        }
    }
    return (int )m;
}

int make_double_adj_mat(double *arr, double *adj_mat, const int size, double eps, int N, bool directed){
    //    takes the 1d array arr, prunes the lowest values less than eps, returns 1 for connection and 0 otherwise
    //    size is length of array, eps is the small amount above which we consider it a connection
    //    takes in adjacency matrix, gives out m
    //    adjacency matrix is 1 for connection, zero otherwise
    //        may be directed, ie unsymmetric
    //        number of edges = total off diag/2 + diags
    int i;
    float m=0; // m is number of edges
    if (directed){
        for (i=0;i<size;i++){
            if (fabs(arr[i]) > eps){ // if a connection
                adj_mat[i] = 1;
                m++;
            } else {
                adj_mat[i] = 0;
            }
        }
    } else {
        for (i=0;i<size;i++){
            if (fabs(arr[i]) > eps){ // if a connection
                adj_mat[i] = 1;
                int row = i/N;
                int col = i%N;
                //            m++;
                if (row==col){
                    m++;
                } else {
                    m+=0.5;
                }
            } else {
                adj_mat[i] = 0;
            }
        }
    }
    return (int )m;
}

void matrix_transpose_d(double *mat_src, double *mat_dest, int N){
    // takes in matrix mat_src, transposes it puts it in mat_dest does not modify mat_src
    // N is length of side of N*N matrix
    // assumes square matrix
    int i, j;
    memset(mat_dest, 0, N*N*sizeof(double));
    for(i=0;i<N;i++){
        for (j=0;j<N;j++){
            
            int ind = i*N + j;
            int ind_t = j*N + i;
            //            printf("i = %i, j = %i\n ind = %i, ind_t = %i\n", i, j, ind, ind_t);
            mat_dest[ind_t] = mat_src[ind];
        }
    }
    
}

void sparse_identity_matrix(sparse_matrix_double *A, int N){
    int i;
    sparse_index row;
    sparse_index col;
    for (i=0;i<N;i++){
        row = i;
        col = i;
        sparse_insert_entry_double(*A, 1.0, row, col);
        printf("inserted val =1 at row = %lli, col=%lli\n", row, col);
    }
    //    sparse_commit(*A);
}

void matrix_transpose_i(int *mat_src, int *mat_dest, int N){
    // takes in matrix mat_src, transposes it puts it in mat_dest does not modify mat_src
    // N is length of side of N*N matrix
    int i, j;
    memset(mat_dest, 0, N*N*sizeof(int));
    for(i=0;i<N;i++){
        for (j=0;j<N;j++){
            
            int ind = i*N + j;
            int ind_t = j*N + i;
            //            printf("i = %i, j = %i\n ind = %i, ind_t = %i\n", i, j, ind, ind_t);
            mat_dest[ind_t] = mat_src[ind];
        }
    }
}

void matrix_add(double *mat_src, double *mat_dest, int N){
    // takes in matrix mat_src, adds it to whats in mat_dest does not modify mat_src
    // N is length of side of N*N matrix
    int i, j;
    for(i=0;i<N;i++){
        for (j=0;j<N;j++){
            int ind = i*N + j;
            mat_dest[ind] += mat_src[ind];
//            mat_dest[ind] /=2;
        }
    }
}
double sparse_get_element_double(sparse_matrix_double A, unsigned i, unsigned j, int ind){
    sparse_index dummy, col;
    double result;
    
    sparse_extract_sparse_row_double(A, i, j, &dummy, 1, &result, &col);
    
    if (col != j && ind ==0){ //matrix is empty
        return 0;
    } else if (col != j){
        // something is broken
        return -1;
    } else {
        
        return result;
    }
}

void load_matrix(double *matrix, const int size, char *filename){
    // loads matrix from text file with space delimiters and end of line for end of row
    // N is num rows and cols, only square matrix
    FILE* fb = fopen(filename, "r");
    //    FILE *fb = fopen(filename, "r");
    if (fb == NULL){
        printf("Error opening file!\n");
        exit(1);
    }
    int i;
    for (i=0;i<size;i++){
        double val;
        if (fscanf(fb, "%lf ", &val) !=1){
            printf("can't read val number in B file i=%i\n", i);
            exit(1);
        }
        matrix[i] = val;
    }
}

void print_double_matrix(double *matrix, int n_rows, int n_cols){
    // n_rows is number of rows, n_cols is number of cols
    int i, j;
    for (i=0;i<n_rows;i++){
        for (j=0;j<n_cols;j++){
            int ind = i*n_rows + j;
            printf("%0.03f ", matrix[ind]);
        }
        printf("\n");
    }
}
void print_int_matrix(int *matrix, int n_rows, int n_cols){
    // n_rows is number of rows, n_cols is number of cols
    int i, j;
    for (i=0;i<n_rows;i++){
        for (j=0;j<n_cols;j++){
            int ind = i*n_rows + j;
            printf("%i ", matrix[ind]);
        }
        printf("\n");
    }
}

void add_gauss_noise(double *matrix, int size, double mu, double sigma){
    // adds gaussian noise to every value of a matrix
    // mean - mu, sd = sigma, rand no added to matrix value
    // modifies matrix in place.
    int i;
    for (i=0;i<size;i++){
        double gn = rand_gauss(mu, sigma);
        matrix[i] += gn;
    }
}

void test_matrix_utilities(void){
    
    // test add gaussian noise
    printf("testing add_gauss_noise\n should be like:\n");
    printf("1.000 2.000 3.000 \n4.000 5.000 6.000\n7.000 8.000 9.000\n");
    double mat[9] = {1,2,3,4,5,6,7,8,9};
    add_gauss_noise(mat, 9, 0.0, 0.2);
    printf("but noisy..\n");
    print_double_matrix(mat, 3, 3);
    
    // test print_double_matrix
    printf("testing print_double_matrix\n should print:\n");
    printf("1.000 2.000 3.000 \n4.000 5.000 6.000\n7.000 8.000 9.000\n");
    printf("printing..\n");
    print_double_matrix(mat, 3, 3);
    
    //test_print_int_matrix
    printf("testing print_int_matrix\n should print:\n");
    printf("1 2 3 \n4 5 6\n7 8 9\n");
    printf("printing..\n");
    int mat_i[9] = {1,2,3,4,5,6,7,8,9};
    print_int_matrix(mat_i, 3, 3);

    //test adjacency matrix
    printf("testing make_adj_mat.. undirected and clean\n");
    const int N = 10;
    double test1[N*N] ={0, 1, 1, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 1, 1, 0, 0, 0, 1,
        0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
        0, 0, 0, 1, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 1, 1, 1,
        0, 0, 0, 0, 0, 0, 1, 0, 1, 0,
        0, 0, 0, 0, 0, 0, 1, 1, 0, 0,
        1, 0, 0, 1, 0, 0, 1, 0, 0, 0};
    print_double_matrix(test1, N, N);
    int *adj_mat;
    adj_mat = (int *)malloc(N*N*sizeof(int));
    int m = make_adj_mat(test1, adj_mat, N*N, 0, N, false);
    printf("m = 12, here m = %i\n", m);
    printf("should be same as adj_mat is below:\n");
    print_int_matrix(adj_mat, N, N);
    
    
    printf("testing make_adj_mat.. directed and clean\n");

    print_double_matrix(test1, N, N);
    m = make_adj_mat(test1, adj_mat, N*N, 0, N, true);
    printf("m = 24, here m = %i\n", m);
    printf("should be same as adj_mat is below:\n");
    print_int_matrix(adj_mat, N, N);
    
    
    printf("testing make_adj_mat.. undirected and noisy\n");
    add_gauss_noise(test1, N*N, 0.0, 0.01);
    print_double_matrix(test1, N, N);
    double eps = array_stddev(test1, N*N);
    m = make_adj_mat(test1, adj_mat, N*N, eps, N, false);
    printf("m = 12, here m = %i\n", m);
    printf("should be same as adj_mat is below:\n");
    print_int_matrix(adj_mat, N, N);
    
    printf("testing make_adj_mat.. directed and noisy\n");
    double test2[N*N] ={0, 1, 1, 0, 0, 0, 0, 0, 0, 0,
        1, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
        0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
        0, 0, 0, 1, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
        0, 0, 0, 0, 0, 0, 1, 0, 1, 0,
        0, 0, 0, 0, 0, 0, 1, 1, 0, 0,
        1, 0, 0, 1, 0, 0, 1, 0, 0, 0};
    add_gauss_noise(test2, N*N, 0.0, 0.01);
    print_double_matrix(test2, N, N);
    eps = array_stddev(test2, N*N);
    m = make_adj_mat(test2, adj_mat, N*N, eps, N, true);
    printf("m = 21, here m = %i\n", m);
    printf("should be same as adj_mat is below:\n");
    print_int_matrix(adj_mat, N, N);
    free(adj_mat);
    
    // testing matrix_transpose_d
    printf("testing matrix_transpose_d\n");
    double arr[16] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
    print_double_matrix(arr, 4, 4);
    printf("transposed should be:\n");
    double *arr_T;
    arr_T = (double *)malloc(16*sizeof(double));
    matrix_transpose_d(arr, arr_T, 4);
    print_double_matrix(arr_T, 4, 4);
    free(arr_T);
    
    // testing matrix_transpose_i
    printf("testing matrix_transpose_i\n");
    int arr_i[16] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
    print_int_matrix(arr_i, 4, 4);
    printf("transposed should be:\n");
    int *arr_iT;
    arr_iT = (int *)malloc(16*sizeof(int));
    matrix_transpose_i(arr_i, arr_iT, 4);
    print_int_matrix(arr_iT, 4, 4);
    free(arr_iT);
    
    // testing matrix_add for doubles only
    printf("testing matrix_add (doubles)\n");
    double matrix1[16] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15};
    print_double_matrix(matrix1, 4, 4);
    printf("plus one each = \n");
    double matrix2[16] = {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1};
    matrix_add(matrix2, matrix1, 4);
    print_double_matrix(matrix1, 4, 4);
    
    //testing load matrix
    printf("testing load matrix..\n");
    char *filename = "/Users/jojo/MSc Stuff/Project/code/test_read_matrix.txt";
    FILE* fb = fopen(filename, "r");
    if (fb == NULL){
        printf("Error opening file!\n");
        exit(1);
    }
    double *matrix;
    matrix = (double *)malloc(16*sizeof(double));
    printf("should be:\n 0.0 0.1 0.2 0.3\n0.4 0.5 0.6 0.7\n0.8 0.9 1.0 1.1\n1.2 1.3 1.4 1.5\n");
    load_matrix(matrix, 16, filename);
    printf("is:\n");
    print_double_matrix(matrix, 4, 4);
    free(matrix);
           
        
    
    
    
}
