//
//  modularity.c
//  expt1
//
//  Created by Joanna Houghton on 19/07/2018.
//  Copyright © 2018 JoSoft. All rights reserved.
// code to measure modularity based on M. E. J. Newman. Modularity and community structure in networks.
// PNAS, 103(23):8577–8582, 2006.
#include <Accelerate/Accelerate.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <string.h>
#include "modularity.h"
#include "utilities.h"
#include "matrix_utilities.h"

void *my_malloc(size_t len){
    void *ptr = malloc(len);
    memset(ptr, 0xff, len);
    return ptr;
}
#define malloc(X) my_malloc(X)

struct node{
    struct node *next;
    struct node *prev;
    double *arr;
    int n_g;
    int *inds;
};

void push(struct node **ptail, double *arr, int n_g, int *inds){
    struct node *new = malloc(sizeof(struct node));
    new->arr = arr;
    new->n_g = n_g;
    new->inds = inds;
    if (*ptail) {
        new->prev = *ptail;
        new->next = (*ptail)->next;
        new->next->prev = new;
        new->prev->next = new;
    } else {
        new->next = new;
        new->prev = new;
    }
    *ptail = new;
}

struct node  * pop(struct node **ptail){

    struct node *old = *ptail;
    if (old->next == old){
        *ptail = NULL;
    } else {
        (*ptail)->prev->next = (*ptail)->next;
        (*ptail)->next->prev = (*ptail)->prev;
        *ptail = (*ptail)->prev;
    }
    return old;
}


double get_Q(double *arr, const int n, const int size, bool refine, bool directed) {
    // takes in weighted directed array of connections, looses weights to form adjacency matrix, calculates modularity matrix, calculates Q for mod matrix then calculates deltaQ for each subsequent division, returns Q_total
    assert(size>0);
    assert(n>0);
    double *mod_mat;
    int m;
    // prepare modularity matrix
    mod_mat = (double *)malloc(size*sizeof(double));
    int *adj_mat;
    adj_mat = (int *)malloc(size*sizeof(int));
    double eps = array_stddev(arr, n*n)*0.5;
    m = make_adj_mat(arr, adj_mat, size, eps, n, directed); // returns number of edges m
    if (m==0){// no edges, fully disconnected
        return -1;
    }
    int *adj_mat_T;
    adj_mat_T = (int *)malloc(size*sizeof(int));
    matrix_transpose_i(adj_mat, adj_mat_T, n);
    make_parent_mod_mat(adj_mat_T, mod_mat, size, n, m, directed);
    free(adj_mat);
    free(adj_mat_T);
    struct node *tail=NULL;
    int *inds;
    inds = (int *)malloc(n*sizeof(int));
    count_arr(inds, n); // makes parent indices
    push(&tail, mod_mat, n, inds);
    double *s;
    s = (double *)malloc(n*sizeof(double));
    double Q = 0;
    int count = 0;
    int n_groups = 0;
    while (tail){
        count ++;
        struct node *child = pop(&tail); // extract next network from stack
        double *child_arr = child->arr;
        int child_ng = child->n_g;
        int *child_inds = child->inds;
        free(child);
        double arg = get_S(child_arr, s, child_ng, m, refine); // calculate next split
        double child_q = 0;
        if (arg !=0){
            child_q = calc_Q(child_arr, child_ng, s, m);
        }
        
        if (child_q> 0){
            Q +=child_q;
            double *kid_sg1;
            double *kid_sg2;
            int size = child_ng*child_ng;
            kid_sg1 = (double *)malloc(size*sizeof(double));
            kid_sg2 = (double *)malloc(size*sizeof(double));

            int n_g1 = child_mod_mats(child_arr, kid_sg1, kid_sg2, size , m, s, directed);
            if (n_g1 == 0){
//                printf("group %i found:\n", n_groups);
//                printIntArr(child_inds, child_ng);
                free(kid_sg1);
                free(kid_sg2);
                free(child_arr);
                free(child_inds);
                n_groups ++;

                continue;
            }
            int n_g2 = child_ng - n_g1;
            int *kid_inds1;
            int *kid_inds2;
            kid_inds1 = (int *)malloc(n_g1*sizeof(int));
            kid_inds2 = (int *)malloc(n_g2*sizeof(int));
            get_child_inds(s, child_inds, kid_inds1, kid_inds2, child_ng);
            push(&tail, kid_sg1, n_g1, kid_inds1);
            push(&tail, kid_sg2, n_g2, kid_inds2);
            free(child_inds);
            free(child_arr);
            
        } else {
            n_groups ++;

            free (child_arr);
            free (child_inds);
        }
    }
    free(s);
    return Q;
}

void make_parent_mod_mat(int *adj_mat, double *mod_mat, const int size, int n, int m, bool directed){
    int i,j;
    int K_i[n], K_j[n];
    for (i=0;i<n; i++){
        int k_i = 0;
        for (j=0;j<n;j++){
            int ind = i*n+j;
            k_i += adj_mat[ind];
        }
        K_i[i] = k_i; // row sums
    }
    for (j=0;j<n; j++){
        int k_j = 0;
        for (i=0;i<n;i++){
            int ind = i*n+j;
            k_j += adj_mat[ind];
        }
        K_j[j] = k_j; // col sums
    }
    
    for (i=0;i<n;i++){
        for (j=0;j<n;j++){
            int ind = i*n+j;
            mod_mat[ind] = (double )adj_mat[ind] - (double )(K_i[i]*K_j[j])/(double )(2*m);
        }
    }
    if (directed){
        double *mod_mat_T;
        mod_mat_T = (double *)malloc(n*n*sizeof(double));
        matrix_transpose_d(mod_mat, mod_mat_T, n);
        matrix_add(mod_mat_T, mod_mat, n);
        free(mod_mat_T);
    }
}

int child_mod_mats(double *mod_mat, double *child_mat1, double *child_mat2, const int size, int m,double *s, bool directed){
    //    makes the modularity matrix for the child using the old mod matrix
    //    B_ij(g) = B_ij - delta_ij * sum_k in g B_ik
    //    and the division given by s
//    returns ng_1
    int n = sqrt(size); // to find number of nodes
    int i,j,k;

    int n_g1 = 0; //number in new group
    int n_g2 = 0;
    int k1_arr[n];
    int k2_arr[n];
    for (k=0;k<n;k++){
        if (s[k] == 1){
            k1_arr[n_g1] =k;
            n_g1 ++; //n_g is number in positive group
        } else {
            k2_arr[n_g2] = k;
            n_g2 ++;
        }
    }
    if (n_g1 == 0 || n_g2 == 0){
//        printf("all in same group, no further division possible");
        return 0;
    }
    if (n_g1 + n_g2 != n){
        printf("error, n_g1 != n_g2");
        exit(1);
    }
    for (i=0;i<n_g1;i++){
        int ind_i = k1_arr[i]; // gives indices in main array of group members k_i
        double sum_i = 0;
        int knos;
        for (knos=0;knos<n_g1; knos++){ // gives sum B_ik
            int k_ind = k1_arr[knos];
            sum_i += mod_mat[ind_i*n + k_ind];
        }
        for (j=0;j<n_g1;j++){
            int ind_j = k1_arr[j];
            int child_ind = i*n_g1 + j;
            int parent_ind = ind_i*n + ind_j;
            child_mat1[child_ind] = mod_mat[parent_ind] - (i==j)*sum_i;
        }
    }
    for (i=0;i<n_g2;i++){
        int ind_i = k2_arr[i];
        double sum_i = 0;
        int knos;
        for (knos=0;knos<n_g2; knos++){ // gives sum B_ik
            int k_ind = k2_arr[knos];
            sum_i += mod_mat[ind_i*n + k_ind];
        }
        for (j=0;j<n_g2;j++){
            int ind_j = k2_arr[j];
            int child_ind = i*n_g2 + j;
            int parent_ind = ind_i*n + ind_j;
            child_mat2[child_ind] = mod_mat[parent_ind] - (i==j)*sum_i;
        }
    
    }
    if (directed){
        double *child_mat1_T;
        double *child_mat2_T;
        child_mat1_T = (double *)malloc(n*n*sizeof(double));
        child_mat2_T = (double *)malloc(n*n*sizeof(double));
        matrix_transpose_d(child_mat1, child_mat1_T, n_g1);
        matrix_transpose_d(child_mat2, child_mat2_T, n_g2);
        matrix_add(child_mat1_T, child_mat1, n_g1);
        matrix_add(child_mat2_T, child_mat2, n_g2);
        free(child_mat1_T);
        free(child_mat2_T);
    }
    return n_g1; // return 1 if successfully got through function, hopefully with the correct matrix values.
}

double eig_max(double *arr, const int size, __CLPK_integer n, double *max_ev){
    // finds largest eigenvalue and corresponding vector from array arr
//    is n 'order of matrix'? LDA - leading dimension of array A - n?
    assert (size>0);

    int lda = n;
    int ldvl = n;
    int ldvr = n;
    int info;
    int lwork=10*size;
    double work[2*size];
    double wr[n], wi[n], vl[ldvl*n], vr[ldvr*n];
    double *old_arr;

    old_arr = (double *)malloc(size*sizeof(double));
    memcpy(old_arr, arr, size*sizeof(double));
    char *jobvl = "V";
    char *jobvr = "N";

    dgeev_(jobvl, jobvr, &n, old_arr, &lda, wr, wi, vl,&ldvl,vr, &ldvr, work, &lwork, &info);
    free(old_arr);
    int k;
    int max_ind = argmax(wr, n);
    
    double max_eig_val = wr[max_ind];
    for (k=0;k<n;k++){ // saves the eigenvector corresponding to the maximum eigenvalue
        max_ev[k] = vl[max_ind*n+k];
    }
    
    if (max_eig_val< 0){
        return 0;
    }
    return max_eig_val;
}



double get_S(double *mod_mat, double *s, int N, int m, bool refine){
    //
    double *max_ev;
    max_ev = malloc(N*sizeof(double));
    double eigval = eig_max(mod_mat, N*N, N, max_ev);
    if (eigval==0){
        free(max_ev);
        return 0;
    }
    int i;
    for (i=0;i<N;i++){
        if (max_ev[i]>0){
            s[i] = 1.0;
        } else {
            s[i] = -1.0;
        }
    }
    free(max_ev);
    if (refine) {
        fine_tuning(mod_mat, s, N, m);
    }
    return eigval;
}

double calc_Q(double *mod_mat, int N, double *s, int m){
//    to calculate the Q value for the full modularity matrix
//    returns Q as 1/(4m) s^T Bs
//    where s is the membership vector, same sign as the eigen vector corresponding
//    to the largest eigenvalue.

    double *ans;
    ans = (double *)malloc(N*sizeof(double));
    memset(ans, 0, N * sizeof(double));
    int size = N*N;
    double *old_arr;
    old_arr = (double *)malloc(size*sizeof(double));
    memcpy(old_arr, mod_mat, size*sizeof(double));
    cblas_dgemv(CblasRowMajor, CblasNoTrans, N, N, 1.0, old_arr, N, s, 1, 1.0, ans, 1);
    double dp = cblas_ddot(N, ans, 1, s, 1);
    double Q =  1/(4*(double )m) * dp;
    free(old_arr);
    free(ans);
    return Q;
}

void fine_tuning(double *mod_mat, double *s, int N, int m){
    // takes matrix and its possible division found using leading eigenvalue
    // find how much moving each vertex to the other group will increase modularity
    // move the one that has the biggest increse, or smallest decrease if no increase is possible. repeat until all have been moved.
    // search all the intermediate states the network went through and find the one with the greatest modularity. start from this state and repeat until no further improvement.
    int i;
    double *sn_largest;
    sn_largest = (double *)malloc(N*sizeof(double));
    double *s_old;
    s_old = (double *)malloc(N*sizeof(double));
    memcpy(s_old, s, N*sizeof(double));
    double Q_old = calc_Q(mod_mat, N, s, m);
    double Qn_largest = -100;
    bool finished = false;
    while (!finished){
        for (i=0;i<N;i++){
            double *sn;
            sn = (double *)malloc(N*sizeof(double));
            memcpy(sn, s_old, N*sizeof(double));
            sn[i] = s[i]*-1;
            double Qn = calc_Q(mod_mat, N, sn, m);
            if (Qn > Qn_largest){
                memcpy(sn_largest, sn, N*sizeof(double));
                Qn_largest = Qn;
            }
            free(sn);
        }
        if (Qn_largest > Q_old){
            Q_old = Qn_largest;
            memcpy(s_old, sn_largest, N*sizeof(double));
        } else {  // no further improvement in modularity score
            finished = true;
            memcpy(s, s_old, N*sizeof(double)); // use the best division so far
        }
    }
    free(sn_largest);
    free(s_old);
}

void get_child_inds(double *s, int *parent_inds, int* child_inds1, int *child_inds2, int parent_n){
    // takes s for division, if n_group = 1, take all s = 1
    // if n_group = 2, take all s = -1
    int i;
    int n_g1=0, n_g2=0;
    for (i=0;i<parent_n;i++){
        if (s[i] ==1){
            child_inds1[n_g1] = parent_inds[i];
            n_g1 ++;
        } else {
            child_inds2[n_g2] = parent_inds[i];
            n_g2 ++;
        }
    }
}

void test_modularity(void){
    // uses simple test case, karate, and jazz
    bool refine = true;
    bool directed = false;
    const int N1 = 10;
    double test1[N1*N1] =
        {0, 1, 1, 0, 0, 0, 0, 0, 0, 1,
        1, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 1, 1, 0, 0, 0, 1,
        0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
        0, 0, 0, 1, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 1, 1, 1,
        0, 0, 0, 0, 0, 0, 1, 0, 1, 0,
        0, 0, 0, 0, 0, 0, 1, 1, 0, 0,
        1, 0, 0, 1, 0, 0, 1, 0, 0, 0};
    
    double test2[N1*N1] =
        {0, 1, 1, 0, 0, 0, 0, 0, 0, 0,
        1, 0, 1, 0, 0, 0, 0, 0, 0, 0,
        1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
        0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
        0, 0, 0, 1, 1, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 1, 1, 0,
        0, 0, 0, 0, 0, 0, 1, 0, 1, 0,
        0, 0, 0, 0, 0, 0, 1, 1, 0, 0,
        1, 0, 0, 1, 0, 0, 1, 0, 0, 0};
    double Q1 = get_Q(test1, N1, N1*N1, refine, directed);
    double Q2 = get_Q(test2, N1, N1*N1, refine, directed);
    const int N3 = 34;
    char *filename3 = "/Users/Jojo/MSc Stuff/Project/code/karate.txt";
    double *B3;
    B3 = malloc(N3*N3*sizeof(double));
    load_matrix(B3, N3*N3, filename3);
    double Q3 = get_Q(B3, N3, N3*N3, refine, directed);
    
    const int N4 = 198;
    char *filename4 = "/Users/Jojo/MSc Stuff/Project/code/jazz.txt";
    double *B4;
    B4 = malloc(N4*N4*sizeof(double));
    load_matrix(B4, N4*N4, filename4);
    double Q4 = get_Q(B4, N4, N4*N4, refine, directed);

    directed = true;
    
    double Q5 = get_Q(test1, N1, N1*N1, refine, directed);
    double Q6 = get_Q(test2, N1, N1*N1, refine, directed);
    double Q7 = get_Q(B3, N3, N3*N3, refine, directed);
    double Q8 = get_Q(B4, N4, N4*N4, refine, directed);
    printf("Without direction:\n");
    printf(" test1 = 0.4896, Q = %0.04f\n test2 = 0.4896, Q = %0.04f\n karate = 0.419, Q = %0.04f\n jazz = 0.442, Q = %0.04f\n", Q1, Q2, Q3, Q4);
    printf("With direction:\n");
    printf("test1 = 0.4896, Q = %0.04f\n test2 = 0.4896, Q = %0.04f\n karate = 0.419, Q = %0.04f\n jazz = 0.442, Q = %0.04f\n", Q5, Q6, Q7, Q8);
    const int N5 = 8;
    double *B5;
    B5 = (double *)malloc(N5*N5*sizeof(double));
    load_matrix(B5, N5*N5, "/Users/Jojo/MSc Stuff/Project/code/B_res48.0_rep1.txt");
    double Q9 = get_Q(B5, N5, N5*N5, refine, directed);
    printf("test 5 B matrix %0.03f\n", Q9);
    free(B3);
    free(B4);
    free(B5);
}
