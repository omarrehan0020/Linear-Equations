function create2Darray(rows) {
    var arr = [];
    for (var i = 0; i < rows; i++)
        arr[i] = [];
    return arr;
}

function swap(arr, ai, aj, bi, bj) {
    let temp = arr[bi][bj];
    arr[bi][bj] = arr[ai][aj];
    arr[ai][aj] = temp;
}

function gauss_elimination(equationArray, vec) {
    // forward elimination
    for (var i = 0; i < equationArray.length - 1; i++) {
        for (var j = i + 1; j < equationArray.length; j++) {
            const factor = -1 * equationArray[j][i] / equationArray[i][i];
            for (var k = i; k < equationArray.length; k++)
                equationArray[j][k] += equationArray[i][k] * factor;
            vec[j] += vec[i] * factor;
        }
        createTable(equationArray, equationArray.length);
    }

    // find the solution --> backward substitution
    const n = equationArray.length - 1;
    var solution = [];
    solution[n] = vec[n] / equationArray[n][n];
    for (var i = n - 1; i >= 0; i--) {
        let sum = 0;
        for (var j = i + 1; j <= n; j++)
            sum += equationArray[i][j] * solution[j];
        solution[i] = (vec[i] - sum) / equationArray[i][i];
    }
    createOneRowInTable(solution, solution.length);
}

function gauss_elimination_with_pivoting(equationArray, vec) {

    // forward elimination
    for (var i = 0; i < equationArray.length - 1; i++) {
        let mx = equationArray[i][i],
            indx = i;
        // getting max pivot 
        for (var row = i; row < equationArray.length; row++) {
            if (equationArray[row][i] > mx) {
                mx = equationArray[row][i];
                indx = row;
            }
        }

        // swapping 
        for (var col = i; col < equationArray.length; col++)
            swap(equationArray, i, col, indx, col);

        // swap in vec also
        let tmp = vec[i];
        vec[i] = vec[indx];
        vec[indx] = tmp;

        // forward elimination
        for (var j = i + 1; j < equationArray.length; j++) {
            const factor = -1 * equationArray[j][i] / equationArray[i][i];
            for (var k = i; k < equationArray.length; k++)
                equationArray[j][k] += equationArray[i][k] * factor;
            vec[j] += vec[i] * factor;
        }
        createTable(equationArray, equationArray.length);
    }

    // find the solution --> backward substitution
    const n = equationArray.length - 1;
    var solution = [];
    solution[n] = vec[n] / equationArray[n][n];
    for (var i = n - 1; i >= 0; i--) {
        let sum = 0;
        for (var j = i + 1; j <= n; j++)
            sum += equationArray[i][j] * solution[j];
        solution[i] = (vec[i] - sum) / equationArray[i][i];
    }

    // return the solution
    createOneRowInTable(solution, solution.length);
}

function gauss_gordan(equationArray, vec) {

    // forward elimination
    for (var i = 0; i < equationArray.length; i++) {
        for (var j = 0; j < equationArray.length; j++) {
            if (i == j)
                continue;
            const factor = -1 * equationArray[j][i] / equationArray[i][i];
            for (var k = i; k < equationArray.length; k++)
                equationArray[j][k] += equationArray[i][k] * factor;
            vec[j] += vec[i] * factor;
        }
        createTable(equationArray, equationArray.length);
    }

    // find the solution --> backward substitution
    const n = equationArray.length - 1;
    var solution = [];
    for (var i = n; i >= 0; i--)
        solution[i] = vec[i] / equationArray[i][i];

    createOneRowInTable(solution, solution.length);
}

function Identity_matrix(rows) {
    var arr = Array(rows).fill(0).map(x => Array(rows).fill(0));
    for (var i = 0; i < rows; i++) {
        arr[i][i] = 1;
    }
    return arr;
}

function downlittle_LU(equationArray, vec) {
    var L = Identity_matrix(equationArray.length);
    addLabel("Start");
    for (var i = 0; i < equationArray.length - 1; i++) {
        addLabel((i + 1) + "  iteration  ");
        for (var j = i + 1; j < equationArray.length; j++) {
            const factor = -1 * equationArray[j][i] / equationArray[i][i];
            for (var k = i; k < equationArray.length; k++)
                equationArray[j][k] += equationArray[i][k] * factor;
            L[j][i] = -1 * factor;
            addLabel("U Matrix");
            createTable(equationArray, equationArray.length);
            addLabel("L Matrix");
            createTable(L, L.length);
        }
    }

    var y = forward_substitution(L, vec);
    addLabel("after forward substitution");
    createOneRowInTable(y, y.length);
    var result = backward_substitution(equationArray, y);
    addLabel("after backward substitution");
    createOneRowInTable(result, result.length);
    return result;
}

function cholesky_LU(equationArray, vec) {
    var n = equationArray.length;
    var L = Array(n).fill(0).map(x => Array(n).fill(0));
    addLabel("Start");
    for (var i = 0; i < n; i++) {
        addLabel((i + 1) + "  iteration  ");
        for (var j = 0; j <= i; j++) {
            let sum = 0;
            if (i == j) {
                for (var k = 0; k < j; k++)
                    sum += Math.pow(L[j][k], 2);
                L[j][j] = Math.sqrt(equationArray[j][j] - sum);
            } else {
                for (var k = 0; k < j; k++)
                    sum += (L[i][k] * L[j][k])
                L[i][j] = (equationArray[i][j] - sum) / L[j][j];
            }
            addLabel("L Matrix");
            createTable(L, L.length);
        }
    }
    var y = forward_substitution(L, vec);
    addLabel("after forward substitution");
    createOneRowInTable(y, y.length);
    var result = backward_substitution(transpose(L), y);
    addLabel("after backward substitution");
    createOneRowInTable(result, result.length);
    return result;
}

function crout_LU(equationArray, vec) {
    var n = equationArray.length;
    var U = Identity_matrix(n + 1);
    var L = create2Darray(n + 1);
    L = Array(n + 1).fill(0).map(x => Array(n + 1).fill(0));
    var sum = 0;
    equationArray = incrementSize(equationArray);
    addLabel("Start");
    for (var i = 1; i <= n; i++) {
        L[i][1] = equationArray[i][1];
        addLabel("L Matrix");
        createTable(normalSize(L), L.length-1);
    }
    for (var j = 2; j <= n; j++) {
        U[1][j] = equationArray[1][j] / L[1][1];
        addLabel("U Matrix");
        createTable(normalSize(U),U.length-1);
    }
    for (var j = 2; j <= n - 1; j++) {
        addLabel( (i) + "  iteration  ");
        for (var i = j; i <= n; i++) {
            sum = 0;
            for (var k = 1; k <= j - 1; k++) {
                sum += (L[i][k] * U[k][j]);
            }
            L[i][j] = equationArray[i][j] - sum;
        }
        for (var k = j + 1; k <= n; k++) {
            sum = 0;
            for (var i = 1; i <= j - 1; i++) {
                sum += (L[j][i] * U[i][k]);
            }
            U[j][k] = (equationArray[j][k] - sum) / L[j][j];
        }
        addLabel("U Matrix");
        createTable(normalSize(U),U.length-1);
        addLabel("L Matrix");
        createTable(normalSize(L), L.length-1);
    }
    sum = 0;
    for (var k = 1; k <= n - 1; k++) {
        sum += (L[n][k] * U[k][n]);
    }
    L[n][n] = equationArray[n][n] - sum;
    addLabel("U Matrix");
    createTable(normalSize(U),U.length-1);
    addLabel("L Matrix");
    createTable(normalSize(L), L.length-1);
    equationArray = normalSize(equationArray);
    U = normalSize(U);
    L = normalSize(L);
    var y = forward_substitution(L, vec);
    addLabel("after forward substitution");
    createOneRowInTable(y, y.length);
    var result = backward_substitution(U, y);
    addLabel("after backward substitution");
    createOneRowInTable(result, result.length);
    return result ;
}

function forward_substitution(equationArray, vec) {
    const n = equationArray.length;
    var solution = [];
    solution[0] = vec[0] / equationArray[0][0];
    for (var i = 0; i < n; i++) {
        let sum = 0;
        for (var j = 0; j < i; j++)
            sum += equationArray[i][j] * solution[j];
        solution[i] = (vec[i] - sum) / equationArray[i][i];
    }
    return solution;
}

function backward_substitution(equationArray, vec) {
    const n = equationArray.length - 1;
    var solution = [];
    solution[n] = vec[n] / equationArray[n][n];
    for (var i = n - 1; i >= 0; i--) {
        let sum = 0;
        for (var j = i + 1; j <= n; j++)
            sum += equationArray[i][j] * solution[j];
        solution[i] = (vec[i] - sum) / equationArray[i][i];
    }
    return solution;
}

function transpose(matrix) {
    const n = matrix.length;
    var solution = create2Darray(n);
    for (var i = 0; i < n; i++) {
        for (var j = 0; j < n; j++) {
            solution[i][j] = matrix[j][i];
        }
    }
    return solution;
}

function isSymetric(equationArray) {
    for (var i = 0; i < equationArray.length; i++) {
        for (var j = 0; j < equationArray.length; j++) {
            if (equationArray[i][j] != equationArray[j][i])
                return false;
        }
    }
    return true;
}

function incrementSize(array) {
    var n = array.length + 1;
    result = create2Darray(n);
    for (var i = 0; i < n - 1; i++) {
        for (var j = 0; j < n - 1; j++) {
            result[i + 1][j + 1] = array[i][j];
        }
    }
    return result;
}

function normalSize(array) {
    var n = array.length - 1;
    result = create2Darray(n);
    for (var i = 0; i < n; i++) {
        for (var j = 0; j < n; j++) {
            result[i][j] = array[i + 1][j + 1];
        }
    }
    return result;
}

function addLabel(text) {
    var x = document.getElementById('results');
    var newlabel = document.createElement("Label");
    newlabel.innerHTML = (text + "\n");
    x.appendChild(newlabel);
}

function gauss_seidel(equation_factors, equations_value, max_degree, number_of_iters,initial_x) {

    var results = [],
        l=1 ;
    while (number_of_iters > 0) {
        
        for (var first_iterator = 0; first_iterator < max_degree; first_iterator++) {
            results[first_iterator] = (equations_value[first_iterator] / equation_factors[first_iterator][first_iterator]);
            for (var second_iterator = 0; second_iterator < max_degree; second_iterator++) {
                if (second_iterator == first_iterator) // not for diagonals
                    continue;
                // the real deal happens below
                results[first_iterator] = results[first_iterator] - ((equation_factors[first_iterator][second_iterator] / equation_factors[first_iterator][first_iterator]) * initial_x[second_iterator]);

            }
            initial_x[first_iterator] = results[first_iterator];
        }
        addLabel('iteration' + l++);
        createOneRowInTable(initial_x,max_degree);
        number_of_iters--;
        
    }
}

function gauss_seidelError(equation_factors, equations_value, max_degree, stopCondition,initial_x) {

    var  results = [],
        newIteration = true;
    var last = initial_x.slice(0),
        l=1 ;
    while (newIteration) {
        for (var first_iterator = 0; first_iterator < max_degree; first_iterator++) {
            results[first_iterator] = (equations_value[first_iterator] / equation_factors[first_iterator][first_iterator]);
            for (var second_iterator = 0; second_iterator < max_degree; second_iterator++) {
                if (second_iterator == first_iterator) // not for diagonals
                    continue;
                // the real deal happens below
                results[first_iterator] = results[first_iterator] - ((equation_factors[first_iterator][second_iterator] / equation_factors[first_iterator][first_iterator]) * initial_x[second_iterator]);
            }
            initial_x[first_iterator] = results[first_iterator];
        }
        // calculating the relative error and decide to make new iteration or not
        for (var i = 0; i < max_degree; i++) {
            var relativeError = (Math.abs((initial_x[i] - last[i]) / initial_x[i])) * 100;
            if (relativeError > stopCondition) {
                newIteration = true;
                break;
            } else {
                newIteration = false;
            }
        }

        last = initial_x.slice(0);
        addLabel('iteration' + l++);
        createOneRowInTable(initial_x,max_degree);
    }
}

function Jacobi_IterationNum(equationArray, equations_value, max_degree, number_of_iters, initial_x) {
    var newGuess_x = [];
    var temp = 0;
    var counter = 1;
    //loop for number of iterations
    while (number_of_iters > 0) {
        //loop for accessing all equations
        for (var i = 0; i < max_degree; i++) {
            //loop for accessing each equation
            for (var j = 0; j < max_degree; j++) {
                if (i != j) {
                    temp += initial_x[j] * equationArray[i][j];
                }
            }
            //get the new X's from the iteration
            newGuess_x[i] = (equations_value[i] - temp) / equationArray[i][i];

            temp = 0;
        }
        //set the initial to the new valuse from the iteration
        initial_x = newGuess_x.slice(0);
        number_of_iters--;
        addLabel("Iteration " + counter);
        createOneRowInTable(initial_x, max_degree);
        counter++;
    }
}

function Jacobi_IterationError(equationArray, equations_value, max_degree, stopCondition, initial_x) {
    var newGuess_x = [];
    var temp = 0;
    var newIteration = true;
    var counter = 1;
    //loop for number of iterations
    while (newIteration) {
        //loop for accessing all equations
        for (var i = 0; i < max_degree; i++) {
            //loop for accessing each equation
            for (var j = 0; j < max_degree; j++) {
                if (i != j) {
                    temp += initial_x[j] * equationArray[i][j];
                }
            }
            //get the new X's from the iteration
            newGuess_x[i] = (equations_value[i] - temp) / equationArray[i][i];
            temp = 0;
        }
        // calculating the relative error and decide to make new iteration or not
        for (var i = 0; i < max_degree; i++) {
            var relativeError = (Math.abs((newGuess_x[i] - initial_x[i]) / newGuess_x[i])) * 100;
            if (relativeError > stopCondition) {
                newIteration = true;
                break;
            } else {
                newIteration = false;
            }
        }
        initial_x = newGuess_x.slice(0);
        addLabel("Iteration " + counter);
        createOneRowInTable(initial_x, max_degree);
        counter++;
    }
}

function handleSolveClicked() {
    var size = parseInt(document.getElementById("size").value);
    var martrixString = document.getElementById("inputEquation").value.split('\n');
    var methodType = document.getElementById("methods").value;
    var stopType = document.getElementById("extraMenu").value;
    var stopValue = document.getElementById("inputCondition").value;
    var intialVAlues = document.getElementById("intailInput").value;
    var equationArray = create2Darray(size);
    var equations_value = create2Darray(1);
    var intialArray = create2Darray(1);
    equationArray = getEquationArray(martrixString, size);
    equations_value = getEquationValues(martrixString, size);
    intialArray = getIntailValues(intialVAlues, size);
    if (methodType == "Jacobi Iteration") {
        if (stopType == "Absolute Relative Error") {
            Jacobi_IterationError(equationArray, equations_value, size, stopValue, intialArray);
        } else {
            Jacobi_IterationNum(equationArray, equations_value, size, stopValue, intialArray);
        }
    } else if (methodType == "Gauss Elimination") {
        gauss_elimination(equationArray, equations_value);
    } else if (methodType == "Gauss Elimination using pivoting.") {
        gauss_elimination_with_pivoting(equationArray, equations_value);
    } else if (methodType == "Gauss Jordan") {
        gauss_gordan(equationArray, equations_value);
    } else if (methodType == "Downlittle Form") {
        downlittle_LU(equationArray, equations_value);
    } else if (methodType == "Cholesky Form") {
        if (isSymetric(equationArray)) {
            cholesky_LU(equationArray, equations_value);
        } else {
            alert("Matrix Must be Symetric")
        }
    } else if (methodType == "Crout Form") {
        crout_LU(equationArray, equations_value);
    }else if (methodType == "Gauss Seidil"){
        if (stopType == "Absolute Relative Error") {
            console.log('here');
            gauss_seidelError(equationArray, equations_value, size, stopValue,intialArray);
        }else {
            gauss_seidel(equationArray, equations_value, size, stopValue,intialArray)
        }
    }
}

function getEquationArray(martrixString, size) {
    var equationMatrix = create2Darray(size);
    for (var i = 0; i < size; i++) {
        var num = martrixString[i].split(' ');
        for (var j = 0; j < size; j++) {
            equationMatrix[i][j] = parseFloat(num[j]);
        }
    }
    return equationMatrix;
}

function getEquationValues(martrixString, size) {
    var equationValues = create2Darray(1);
    for (var i = 0; i < size; i++) {
        var num = martrixString[i].split(' ');
        equationValues[i] = parseFloat(num[size]);
    }
    return equationValues;
}

function getIntailValues(matrix, size) {
    var equationValues = create2Darray(1);
    var num = matrix.split(' ');
    for (var i = 0; i < size; i++) {
        equationValues[i] = parseFloat(num[i]);
    }
    return equationValues;
}

function handlefile() {

    var fileSelected = document.getElementById('inputfile').files[0];
    var type = (fileSelected.name).split('.').pop();
    var fr = new FileReader();
    if (type == 'txt') {
        fr.onload = function() {
            document.getElementById('inputEquation').value = fr.result;
        }
        fr.readAsText(fileSelected);
    } else {
        alert("upload txt files only");
    }
    this.files = null;
}

function createTable(matrix, size) {
    var x = document.getElementById('results');
    var table = document.createElement('table');
    console.log(matrix[0].length);
    for (var i = 0; i < size; i++) {
        var row = document.createElement('tr');
        for (var j = 0; j < matrix[0].length; j++) {
            var td = document.createElement('td');
            var value = document.createTextNode(parseFloat(matrix[i][j]).toFixed(7));
            td.appendChild(value);
            row.appendChild(td);
        }
        table.appendChild(row);
    }
    x.appendChild(table);
}

function createOneRowInTable(matrix, size) {
    var x = document.getElementById('results');
    var table = document.createElement('table');
    var row = document.createElement('tr');
    for (var j = 0; j < size; j++) {
        var td = document.createElement('td');
        var value = document.createTextNode(parseFloat(matrix[j]).toFixed(7));
        td.appendChild(value);
        row.appendChild(td);
    }
    table.appendChild(row);
    x.appendChild(table);
}