//
//  utilities.h
//  expt1
//
//  Created by Joanna Houghton on 07/08/2018.
//  Copyright © 2018 JoSoft. All rights reserved.
//

#ifndef utilities_h
#define utilities_h
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdbool.h>

void printIntArr(int *arr, int len);
void printDoubleArr(double *arr, int len);
void printfDoubleArr(FILE *f, int t, double *arr, int len);
void shuffle_d(double *arr, int t);
void shuffle_i(int *arr, int t);
double rand_gauss(double mean, double sd);
void count_arr(int *count, int len);
int argmax(double *arr, const int n);
bool is_in(int *array, int query, int len);
double sum_double_array(double *arr, int n);
double sum_int_array(int *arr, int n);
double array_stddev(double *array, int len);
double array_mean(double *array, int len);
double std_dev(double *arr, const int size);
double mean(double *arr, const int size);
int arr_row_sum(int *arr, int row_start, int row_end);
int arr_col_sum(int *arr, int col_start, const int size, int n);
void test_utilities(void);
double total_absolute_weight_array(double *array, int len);
void invert_all_elements(double *array, int len, double *inv_array);
void multiply_all_elements_d(double *input_array, int len, double *result_array, double multiplier);
void multiply_all_elements_i(int *input_array, int len, double *result_array, double multiplier);
double chi_squared_count(int *array, int len);
double chi_squared_norm(double *array, int len);
#endif /* utilities_h */
