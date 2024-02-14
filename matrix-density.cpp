#include <iostream>

/* constants corresponding to program parameters */
const int R = 3;    // number of rows of the model
const int C = 4;    // number of cloumns of the model; it is assumed that 5 >= C >= R
const int maxMatrices = 4097;  // maximum number of 0/1 matrices the program can handle
const int maxNumTypes = 6;    // maximum number of types the program can handle
const int maxFlagsInList = 100;  // maximum number of distinct flags the program can handle in a given flag list
const bool monotone = true;  // set true if we only wish to consider monotone matrices
const bool useOneByOneTypes = false; // set true if one by one types (ther eare two of them) are required
const bool useOneByTwoTypes = true;

/* global variables */      
int perm[C+1][120][C];   // perm[n] consists of all permutations of {0..n-1}. For 0 <= t < n! , perm[n][t] is a single parmutation and perm[n][t][i] is the i'th element of the permutation
int matrix[maxMatrices][R][C];  // matrix[t] is a single matrix
int numMatrices;               // actual number of matrices
int numTypes;                // actual number of types
int flagList[maxNumTypes][maxFlagsInList][4][4]; // flagList[t] is a flagList, flaglist[t][j] is th j'th flag in the list, and it is represented by a matrix of size at most 3 * 3.
                                                 // The last row/column denotes whether the row/column is marked.
												 // for example: For a 2 \times 3 flag, if flagList[t][j][1][3] != 0 it meast that row "1"  is marked
												 // Another example: For a 2 \times 2 flag, if flagList[t][j][2][0] = 0 it meast that column "0"  is unmarked
int flagListSize[maxNumTypes];  //  flagListSize[t] is the number of flags in flagList t.
int SDarray[maxNumTypes][maxFlagsInList][maxFlagsInList];  // SDarray[i] is a square matrix indexed by the elements of a flag list, i is the serial number of the flag list.
int targetDensities[maxMatrices];   // targetDensities[t] represents the density of the target object in matrix t. Our target object are all the 2*2 matrices except [00|01].

/* printing functions */

void printModelSize() {
	printf("Number of matrices in the model is %d\n", numMatrices);
}

void printFlagListsQuantities() {
	for (int i = 0; i < numTypes; i++)
		printf("The size of flag list #%d is %d\n", i, flagListSize[i]);
}

/* utility functions */

int fact(int n) {
	int f = 1;
	for (int i = 2; i <= n; i++)
		f *= i;
	return f;
}

/* operational functions */

void loadPermutations() {
	int fact = 1;
	for (int l = 1; l <= std::max(R,C); l++) {
		fact *= l;
		int n = l - 1;
		int t = 0;
		for (int j = 0; j < fact; j++)
			for (int k = l - 1; k >= 0; k--) {
				for (int q = 0; q < k; q++)
					perm[l][t][q] = perm[l - 1][j][q];
				perm[l][t][k] = n;
				for (int q = k + 1; q < l; q++)
					perm[l][t][q] = perm[l - 1][j][q - 1];
				t++;
			}
	}
}

bool createMatrix(int w[]) {
	int t = 0;
	for (int i = 0; i < R; i++)
		for (int j = 0; j < C; j++) {
			matrix[numMatrices][i][j] = w[t];
			t++;
		}
	if (!monotone)
		return true;
	for (int i = 0; i < R; i++)
		for (int j = 0; j < C - 1; j++)
			if (matrix[numMatrices][i][j] == 1 && matrix[numMatrices][i][j + 1] == 0)
				return false;
	for (int j = 0; j < C; j++)
		for (int i = 0; i < R - 1; i++)
			if (matrix[numMatrices][i][j] == 1 && matrix[numMatrices][i + 1][j] == 0)
				return false;
	return true;
}

void constructMatrices() {
	int word[100];
	numMatrices = 0;
	int numCrossPairs = R * C;
	for (int i = 0; i < numCrossPairs; i++)
		word[i] = 0;
	createMatrix(word);
	numMatrices++;
	while (1) {
		int i = 0;
		while (word[i] == 1 && i < numCrossPairs) {
			word[i] = 0;
			i++;
		}
		if (i == numCrossPairs)
			break;
		word[i]++;
		if (createMatrix(word))
			numMatrices++;
	}
}

void computeTargetDensities() {
	for (int g = 0; g < numMatrices; g++) {
		for (int i1 = 0; i1 < R; i1++)
			for (int i2 = i1 + 1; i2 < R; i2++)
				for (int j1 = 0; j1 < C; j1++)
					for (int j2 = j1 + 1; j2 < C; j2++)
						if (matrix[g][i1][j1] == 0 && matrix[g][i1][j2] == 0 && matrix[g][i2][j1] == 0 && matrix[g][i2][j2] == 1)
							targetDensities[g]++;
		targetDensities[g] = R * (R - 1) / 2 * C * (C - 1) / 2 - targetDensities[g];
	}
}

void createOneByOneTypeFlags() {  // For sigma = (0) and for sigma=(1), creates the flag list F_{2,2}^sigma
	int mat[2][2];
	int typeNum;
	int count[] = { 0,0 };
	for (int i = 0; i < 2; i++)    // i will be the marked row 
		for (int j = 0; j < 2; j++)  // j will be the marked column
			for (int i1 = 0; i1 < 2; i1++)
				for (int i2 = 0; i2 < 2; i2++)
					for (int j1 = 0; j1 < 2; j1++)
						for (int j2 = 0; j2 < 2; j2++) {
							if (monotone && (i1 > i2 || i1 > j1 || i2 > j2 || j1 > j2))
								continue;
							mat[0][0] = i1;
							mat[0][1] = i2;
							mat[1][0] = j1;
							mat[1][1] = j2;
							typeNum = mat[i][j];  // decides if sigma=(0) or sigma=(1) for this matrix and markings
							flagList[typeNum][count[typeNum]][0][0] = mat[0][0];
							flagList[typeNum][count[typeNum]][0][1] = mat[0][1];
							flagList[typeNum][count[typeNum]][1][0] = mat[1][0];
							flagList[typeNum][count[typeNum]][1][1] = mat[1][1];
							flagList[typeNum][count[typeNum]][2][0] = -1;
							flagList[typeNum][count[typeNum]][2][1] = -1;
							flagList[typeNum][count[typeNum]][0][2] = -1;
							flagList[typeNum][count[typeNum]][1][2] = -1;
							flagList[typeNum][count[typeNum]][2][2] = -1;
							flagList[typeNum][count[typeNum]][i][2] = 1;
							flagList[typeNum][count[typeNum]][2][j] = 1;
							count[typeNum]++;
						}
	flagListSize[numTypes] = count[numTypes];
	flagListSize[numTypes + 1] = count[numTypes + 1];
	numTypes += 2;
}

void createOneByTwoTypeFlags() {  // for sigma = (0,0) or (0,1) or (1,0) or (1,1) creates the flag list F_{2,3}^sigma
	int mat[2][3];
	int typeNum;
	int count[] = { 0,0,0,0};
	for (int ll = 0; ll < 2; ll++)
		for (int lr1 = 0; lr1 < 3; lr1++)
			for (int lr2 = lr1 + 1; lr2 < 3; lr2++)
				for (int i1 = 0; i1 < 2; i1++)
					for (int i2 = 0; i2 < 2; i2++)
						for (int i3 = 0; i3 < 2; i3++)
							for (int j1 = 0; j1 < 2; j1++)
								for (int j2 = 0; j2 < 2; j2++)
									for (int j3 = 0; j3 < 2; j3++) {
										if (monotone && (i1 > j1 || i2 > j2 || i3 > j3 || i2 < i1 || i2 > i3 || j2 < j1 || j2 > j3))
											continue;
										mat[0][0] = i1;
										mat[0][1] = i2;
										mat[0][2] = i3;
										mat[1][0] = j1;
										mat[1][1] = j2;
										mat[1][2] = j3;
										typeNum = mat[ll][lr1] + 2 * mat[ll][lr2];
										flagList[typeNum + numTypes][count[typeNum]][0][0] = mat[0][0];
										flagList[typeNum + numTypes][count[typeNum]][0][1] = mat[0][1];
										flagList[typeNum + numTypes][count[typeNum]][0][2] = mat[0][2];
										flagList[typeNum + numTypes][count[typeNum]][1][0] = mat[1][0];
										flagList[typeNum + numTypes][count[typeNum]][1][1] = mat[1][1];
										flagList[typeNum + numTypes][count[typeNum]][1][2] = mat[1][2];
										flagList[typeNum + numTypes][count[typeNum]][2][0] = -1;
										flagList[typeNum + numTypes][count[typeNum]][2][1] = -1;
										flagList[typeNum + numTypes][count[typeNum]][2][2] = -1;
										flagList[typeNum + numTypes][count[typeNum]][0][3] = -1;
										flagList[typeNum + numTypes][count[typeNum]][1][3] = -1;
										flagList[typeNum + numTypes][count[typeNum]][2][3] = -1;
										flagList[typeNum + numTypes][count[typeNum]][ll][3] = 1;
										flagList[typeNum + numTypes][count[typeNum]][2][lr1] = 1;
										flagList[typeNum + numTypes][count[typeNum]][2][lr2] = 2;
										count[typeNum]++;
									}
	for(int i=0; i <4; i++)
		flagListSize[numTypes+i] = count[i];
	numTypes += 4;
}

void populateSDArray(int g) {
	// initialize to zero all the joint densities in the matrix
	for (int t = 0; t < numTypes; t++)
		for (int i = 0; i < flagListSize[t]; i++)
			for (int j = 0; j < flagListSize[t]; j++)
				SDarray[t][i][j] = 0;

	//Now loop over all permutations of vertices of H. For each permutation check if it induces a flag for the given type
	int n1fact = fact(R);
	int n2fact = fact(C);
	for (int p = 0; p < n1fact; p++)
		for (int q = 0; q < n2fact; q++) {
			if (useOneByOneTypes) {
				int labeledRow = perm[R][p][0];
				int labeledColumn = perm[C][q][0];
				int t = matrix[g][labeledRow][labeledColumn];
				int unlabeledRowFirstFlag = perm[R][p][1];
				int unlabeledColumnFirstFlag = perm[C][q][1];
				int unlabeledRowSecondFlag = perm[R][p][2];
				int unlabeledColumnSecondFlag = perm[C][q][2];
				int flag[3][3];
				int x, y;
				int firstRow, secondRow, firstColumn, secondColumn;
				firstRow = (labeledRow < unlabeledRowFirstFlag) ? labeledRow : unlabeledRowFirstFlag;
				secondRow = (labeledRow < unlabeledRowFirstFlag) ? unlabeledRowFirstFlag : labeledRow;
				firstColumn = (labeledColumn < unlabeledColumnFirstFlag) ? labeledColumn : unlabeledColumnFirstFlag;
				secondColumn = (labeledColumn < unlabeledColumnFirstFlag) ? unlabeledColumnFirstFlag : labeledColumn;
				flag[0][0] = matrix[g][firstRow][firstColumn];
				flag[0][1] = matrix[g][firstRow][secondColumn];
				flag[1][0] = matrix[g][secondRow][firstColumn];
				flag[1][1] = matrix[g][secondRow][secondColumn];
				flag[0][2] = -1;
				flag[1][2] = -1;
				flag[2][0] = -1;
				flag[2][1] = -1;
				flag[2][2] = -1;
				if (firstRow == labeledRow)
					flag[0][2] = 1;
				else
					flag[1][2] = 1;
				if (firstColumn == labeledColumn)
					flag[2][0] = 1;
				else
					flag[2][1] = 1;
				for (int f = 0; f < flagListSize[t]; f++) {
					//check if flagList[t][i] is identical to flag
					int good = true;
					for (int i = 0; i < 3 && good; i++)
						for (int j = 0; j < 3 && good; j++)
							if (flagList[t][f][i][j] != flag[i][j])
								good = false;
					if (good) {
						x = f;
						break;
					}
				}

				firstRow = (labeledRow < unlabeledRowSecondFlag) ? labeledRow : unlabeledRowSecondFlag;
				secondRow = (labeledRow < unlabeledRowSecondFlag) ? unlabeledRowSecondFlag : labeledRow;
				firstColumn = (labeledColumn < unlabeledColumnSecondFlag) ? labeledColumn : unlabeledColumnSecondFlag;
				secondColumn = (labeledColumn < unlabeledColumnSecondFlag) ? unlabeledColumnSecondFlag : labeledColumn;
				flag[0][0] = matrix[g][firstRow][firstColumn];
				flag[0][1] = matrix[g][firstRow][secondColumn];
				flag[1][0] = matrix[g][secondRow][firstColumn];
				flag[1][1] = matrix[g][secondRow][secondColumn];
				flag[0][2] = -1;
				flag[1][2] = -1;
				flag[2][0] = -1;
				flag[2][1] = -1;
				flag[2][2] = -1;
				if (firstRow == labeledRow)
					flag[0][2] = 1;
				else
					flag[1][2] = 1;
				if (firstColumn == labeledColumn)
					flag[2][0] = 1;
				else
					flag[2][1] = 1;
				for (int f = 0; f < flagListSize[t]; f++) {
					int good = true;
					for (int i = 0; i < 3 && good; i++)
						for (int j = 0; j < 3 && good; j++)
							if (flagList[t][f][i][j] != flag[i][j])
								good = false;
					if (good) {
						y = f;
						break;
					}
				}
				SDarray[t][x][y]++;
			}


			if (useOneByTwoTypes) {
				int labeledRow = perm[R][p][0];
				int labeledColumn1 = perm[C][q][0];
				int labeledColumn2 = perm[C][q][1];
				int t = useOneByOneTypes ? 2 : 0;
				if (labeledColumn1 < labeledColumn2)
					t +=  matrix[g][labeledRow][labeledColumn1] + 2 * matrix[g][labeledRow][labeledColumn2];
				else
					t +=  matrix[g][labeledRow][labeledColumn2] + 2 * matrix[g][labeledRow][labeledColumn1];
				int unlabeledRowFirstFlag = perm[R][p][1];
				int unlabeledColumnFirstFlag = perm[C][q][2];
				int unlabeledRowSecondFlag = perm[R][p][2];
				int unlabeledColumnSecondFlag = perm[C][q][3];
				int firstColumn, secondColumn, thirdColumn;
				int firstRow = (labeledRow < unlabeledRowFirstFlag) ? labeledRow : unlabeledRowFirstFlag;
				int secondRow = (labeledRow < unlabeledRowFirstFlag) ? unlabeledRowFirstFlag : labeledRow;
				if (labeledColumn1 < labeledColumn2) {
					firstColumn = labeledColumn1;
					secondColumn = labeledColumn2;
				}
				else {
					firstColumn = labeledColumn2;
					secondColumn = labeledColumn1;
				}
				if (unlabeledColumnFirstFlag > secondColumn)
					thirdColumn = unlabeledColumnFirstFlag;
				else if (unlabeledColumnFirstFlag > firstColumn) {
					thirdColumn = secondColumn;
					secondColumn = unlabeledColumnFirstFlag;
				}
				else {
					thirdColumn = secondColumn;
					secondColumn = firstColumn;
					firstColumn = unlabeledColumnFirstFlag;
				}
				int flag[3][4];
				int x, y;
				flag[0][0] = matrix[g][firstRow][firstColumn];
				flag[0][1] = matrix[g][firstRow][secondColumn];
				flag[0][2] = matrix[g][firstRow][thirdColumn];
				flag[1][0] = matrix[g][secondRow][firstColumn];
				flag[1][1] = matrix[g][secondRow][secondColumn];
				flag[1][2] = matrix[g][secondRow][thirdColumn];
				flag[0][3] = -1;
				flag[1][3] = -1;
				flag[2][0] = -1;
				flag[2][1] = -1;
				flag[2][2] = -1;
				flag[2][3] = -1;
				if (firstRow == labeledRow)
					flag[0][3] = 1;
				else
					flag[1][3] = 1;
				if (firstColumn == unlabeledColumnFirstFlag) {
					flag[2][1] = 1;
					flag[2][2] = 2;
				}
				else if (secondColumn == unlabeledColumnFirstFlag) {
					flag[2][0] = 1;
					flag[2][2] = 2;
				}
				else {
					flag[2][0] = 1;
					flag[2][1] = 2;
				}
				for (int f = 0; f < flagListSize[t]; f++) {
					//check if flagList[t][i] is identical to flag
					int good = true;
					for (int i = 0; i < 3 && good; i++)
						for (int j = 0; j < 4 && good; j++)
							if (flagList[t][f][i][j] != flag[i][j])
								good = false;
					if (good) {
						x = f;
						break;
					}
				}

				firstRow = (labeledRow < unlabeledRowSecondFlag) ? labeledRow : unlabeledRowSecondFlag;
				secondRow = (labeledRow < unlabeledRowSecondFlag) ? unlabeledRowSecondFlag : labeledRow;
				if (labeledColumn1 < labeledColumn2) {
					firstColumn = labeledColumn1;
					secondColumn = labeledColumn2;
				}
				else {
					firstColumn = labeledColumn2;
					secondColumn = labeledColumn1;
				}
				if (unlabeledColumnSecondFlag > secondColumn)
					thirdColumn = unlabeledColumnSecondFlag;
				else if (unlabeledColumnSecondFlag > firstColumn) {
					thirdColumn = secondColumn;
					secondColumn = unlabeledColumnSecondFlag;
				}
				else {
					thirdColumn = secondColumn;
					secondColumn = firstColumn;
					firstColumn = unlabeledColumnSecondFlag;
				}
				flag[0][0] = matrix[g][firstRow][firstColumn];
				flag[0][1] = matrix[g][firstRow][secondColumn];
				flag[0][2] = matrix[g][firstRow][thirdColumn];
				flag[1][0] = matrix[g][secondRow][firstColumn];
				flag[1][1] = matrix[g][secondRow][secondColumn];
				flag[1][2] = matrix[g][secondRow][thirdColumn];
				flag[0][3] = -1;
				flag[1][3] = -1;
				flag[2][0] = -1;
				flag[2][1] = -1;
				flag[2][2] = -1;
				flag[2][3] = -1;
				if (firstRow == labeledRow)
					flag[0][3] = 1;
				else
					flag[1][3] = 1;
				if (firstColumn == unlabeledColumnSecondFlag) {
					flag[2][1] = 1;
					flag[2][2] = 2;
				}
				else if (secondColumn == unlabeledColumnSecondFlag) {
					flag[2][0] = 1;
					flag[2][2] = 2;
				}
				else {
					flag[2][0] = 1;
					flag[2][1] = 2;
				}
				for (int f = 0; f < flagListSize[t]; f++) {
					int good = true;
					for (int i = 0; i < 3 && good; i++)
						for (int j = 0; j < 4 && good; j++)
							if (flagList[t][f][i][j] != flag[i][j])
								good = false;
					if (good) {
						y = f;
						break;
					}
				}
				SDarray[t][x][y]++;
			}
		}
}


void writeSDP() {
	FILE* outfile;
	fopen_s(&outfile, monotone ? "monotone.dat-s" : "emptyset.dat-s", "w");

	int countValidFlags = 0;
	for (int i = 0; i < numTypes; i++)
		if (flagListSize[i] > 0)
			countValidFlags++;

	int numConstraints = 0;
	for (int i = 0; i < numMatrices; i++)
		if (targetDensities[i] >= 0)
			numConstraints++;

	fprintf(outfile, "%d\n", numConstraints); // first line contains the number of constraints
	fprintf(outfile, "%d\n", countValidFlags + 1); // the number of blocks (corrsponds to the number of SD matrices plus one additional block for the slacks

	for (int i = 0; i < numTypes; i++)
		if (flagListSize[i] > 0)
			fprintf(outfile, "%d ", flagListSize[i]);  // writing the size of each block
	fprintf(outfile, "%d\n", -numConstraints - 1); // the size of the last block which is a diagonal block so preceded with a minus sign

	//Now write the density in each matrix
	for (int i = 0; i < numMatrices; i++)
			fprintf(outfile, "%d ", targetDensities[i]);  
	fprintf(outfile, "\n");

	// now write the slack target line
	fprintf(outfile, "0 %d 1 1 1\n", countValidFlags + 1);

	// For each matrix in the model and for each block, write the nonzero entries
	int count = -1;
	for (int g = 0; g < numMatrices; g++) {
		if (targetDensities[g] < 0)
			continue;
		count++;
		int c = -1;
		populateSDArray(g);
		for (int t = 0; t < numTypes; t++) {
			if (flagListSize[t] > 0)
				c++;
			for (int i = 0; i < flagListSize[t]; i++)
				for (int j = i; j < flagListSize[t]; j++)
					if (SDarray[t][i][j] != 0)
						fprintf(outfile, "%d %d %d %d %d\n", count + 1, c + 1, i + 1, j + 1, SDarray[t][i][j]);   // perhaps the values should be normalized with some gcd; this should have no effect on the results
		}
		// now write entriees for the last block
		fprintf(outfile, "%d %d 1 1 1\n", count + 1, countValidFlags + 1);
		fprintf(outfile, "%d %d %d %d 1\n", count + 1, countValidFlags + 1, count + 2, count + 2);
	}
	fclose(outfile);
}


int main()
{
	loadPermutations();
	constructMatrices();
	printModelSize();
	computeTargetDensities();
	if (useOneByOneTypes)
		createOneByOneTypeFlags();
	if (useOneByTwoTypes)
		createOneByTwoTypeFlags();
	printFlagListsQuantities();
	writeSDP();
}