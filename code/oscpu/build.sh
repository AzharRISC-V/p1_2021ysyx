#!/bin/bash

VERSION="1.18"

help() {
    echo "Version v"$VERSION
    echo "Usage:"
    echo "build.sh [-e project_name] [-b] [-t top_file] [-s] [-a parameters_list] [-f] [-l] [-g] [-w] [-c] [-d] [-m] [-r test_cases]"
    echo "Description:"
    echo "-e: Specify a example project. For example: -e counter. If not specified, the default directory \"cpu\" will be used."
    echo "-b: Build project using verilator and make tools automatically. It will generate the \"build\"(difftest) or \"build_test\" subfolder under the project directory."
    echo "-t: Specify a file as verilog top file. If not specified, the default filename \"top.v\" will be used. This option is invalid when connected difftest."
    echo "-s: Run simulation program. Use the \"build_test\" or \"build\"(difftest) folder as work path."
    echo "-a: Parameters passed to the simulation program. For example: -a \"1 2 3 ......\". Multiple parameters require double quotes."
    echo "-f: C++ compiler arguments for makefile. For example: -f \"-DGLOBAL_DEFINE=1 -ggdb3\". Multiple parameters require double quotes. This option is invalid when connected difftest."
    echo "-l: C++ linker arguments for makefile. For example: -l \"-ldl -lm\". Multiple parameters require double quotes. This option is invalid when connected difftest."
    echo "-g: Debug the simulation program with GDB. This option is invalid when connected difftest."
    echo "-w: Open the latest waveform file(.vcd) using gtkwave under work path. Use the \"build_test\" or \"build\"(difftest) folder as work path."
    echo "-c: Delete \"build\" and \"build_test\" folders under the project directory."
    echo "-d: Connect to XiangShan difftest framework."
    echo "-m: Parameters passed to the difftest makefile. For example: -m \"EMU_TRACE=1 EMU_THREADS=4\". Multiple parameters require double quotes."
    echo "-r: Run all test cases of the specified directory in the \"bin\" directory. For example: -r \"case1 case2\". This option requires the project to be able to connect to difftest."
    exit 0
}

create_soft_link() {
    mkdir ${1} 1>/dev/null 2>&1
    find -L ${1} -type l -delete
    FILES=`eval "find ${2} -mindepth 1 -maxdepth 2 -name ${3}"`
    for FILE in ${FILES[@]}
    do
        eval "ln -s \"`realpath --relative-to="${1}" "$FILE"`\" \"${1}/${FILE##*/}\" 1>/dev/null 2>&1"
    done
}

create_bin_soft_link() {
    find -L $BUILD_PATH -maxdepth 1 -type l -delete
    FOLDERS=`find bin -mindepth 1 -maxdepth 1 -type d`
    for FOLDER in ${FOLDERS[@]}
    do
        SUBFOLDER=${FOLDER##*/}
        eval "ln -s \"`realpath --relative-to="$BUILD_PATH" "$OSCPU_PATH/$FOLDER"`\" \"$BUILD_PATH/${FOLDER##*/}\" 1>/dev/null 2>&1"
    done

    # create soft link ($BUILD_PATH/*.bin -> $OSCPU_PATH/$BIN_FOLDER/*.bin). Why? Because of laziness!
    create_soft_link $BUILD_PATH $OSCPU_PATH/$BIN_FOLDER \"*.bin\"
}

compile_dramsim3() {
    if [[ ! -f $OSCPU_PATH/$DRAMSIM3_FOLDER/build/libdramsim3.a ]]; then
        [[ ! `dpkg -l | grep cmake` ]] && sudo apt-get --yes install cmake
        mkdir $OSCPU_PATH/$DRAMSIM3_FOLDER/build
        cd $OSCPU_PATH/$DRAMSIM3_FOLDER/build
        cmake -D COSIM=1 ..
        make
        if [ $? -ne 0 ]; then
            echo "Failed to build dramsim3!!!"
            exit 1
        fi
        cd $OSCPU_PATH
    fi
}

compile_nemu() {
    if [[ ! -f $NEMU_HOME/build/riscv64-nemu-interpreter-so ]]; then
        cd $NEMU_HOME
        make riscv64-ysyx-ref_defconfig
        make
        if [ $? -ne 0 ]; then
            echo "Failed to build nemu!!!"
            exit 1
        fi
        cd $OSCPU_PATH
    fi
}

compile_chisel() {
    if [[ -f $PROJECT_PATH/build.sc ]]; then
        # create soft link ($PROJECT_PATH/difftest -> $LIBRARIES_HOME/difftest)
        if [[ ! -L $PROJECT_PATH/$DIFFTEST_FOLDER ]]; then
            eval "ln -s \"`realpath --relative-to="$PROJECT_PATH" "$LIBRARIES_HOME"`/$DIFFTEST_FOLDER\" \"$PROJECT_PATH/$DIFFTEST_FOLDER\" 1>/dev/null 2>&1"
        fi

        cd $PROJECT_PATH
        mkdir vsrc 1>/dev/null 2>&1
        mill -i oscpu.runMain TopMain -td vsrc
        cd $OSCPU_PATH
    fi
}

compile_difftest() {
    cd $DIFFTEST_HOME
    make -s DESIGN_DIR=$PROJECT_PATH $DIFFTEST_PARAM
    if [ $? -ne 0 ]; then
        echo "Failed to build difftest!!!"
        exit 1
    fi
    cd $OSCPU_PATH
}

build_diff_proj() {
    compile_dramsim3
    compile_nemu
    compile_chisel

    # Refresh the modification time of the top file, otherwise some changes to the RTL source code will not take effect in next compilation.
    touch -m `find $BUILD_PATH -name $DIFFTEST_TOP_FILE` 1>/dev/null 2>&1
    # create soft link ($BUILD_PATH/*.v -> $PROJECT_PATH/$VSRC_FOLDER/*.v)
    create_soft_link $BUILD_PATH $PROJECT_PATH/$VSRC_FOLDER \"*.v\"

    compile_difftest
}

build_proj() {
    cd $PROJECT_PATH

    # get all .cpp files
    CSRC_LIST=`find $PROJECT_PATH/$CSRC_FOLDER -name "*.cpp"`
    for CSRC_FILE in ${CSRC_LIST[@]}
    do
        CSRC_FILES="$CSRC_FILES $CSRC_FILE"
    done
    # get all vsrc subfolders
    VSRC_SUB_FOLDER=`find $VSRC_FOLDER -type d`
    for SUBFOLDER in ${VSRC_SUB_FOLDER[@]}
    do
        INCLUDE_VSRC_FOLDERS="$INCLUDE_VSRC_FOLDERS -I$SUBFOLDER"
    done
    # get all csrc subfolders
    CSRC_SUB_FOLDER=`find $PROJECT_PATH/$CSRC_FOLDER -type d`
    for SUBFOLDER in ${CSRC_SUB_FOLDER[@]}
    do
        INCLUDE_CSRC_FOLDERS="$INCLUDE_CSRC_FOLDERS -I$SUBFOLDER"
    done

    # compile
    mkdir $BUILD_FOLDER 1>/dev/null 2>&1
    eval "verilator --x-assign unique --cc --exe --trace --assert -O3 -CFLAGS \"-std=c++11 -Wall $INCLUDE_CSRC_FOLDERS $CFLAGS\" $LDFLAGS -o $PROJECT_PATH/$BUILD_FOLDER/$EMU_FILE \
        -Mdir $PROJECT_PATH/$BUILD_FOLDER/emu-compile $INCLUDE_VSRC_FOLDERS --build $V_TOP_FILE $CSRC_FILES"
    if [ $? -ne 0 ]; then
        echo "Failed to run verilator!!!"
        exit 1
    fi

    cd $OSCPU_PATH
}

# Initialize variables
OSCPU_PATH=$(dirname $(readlink -f "$0"))
MYINFO_FILE=$OSCPU_PATH"/myinfo.txt"
EMU_FILE="emu"
PROJECT_FOLDER="cpu"
BUILD_FOLDER="build_test"
DIFF_BUILD_FOLDER="build"
VSRC_FOLDER="vsrc"
CSRC_FOLDER="csrc"
BIN_FOLDER="bin"
BUILD="false"
V_TOP_FILE="top.v"
SIMULATE="false"
CHECK_WAVE="false"
CLEAN="false"
PARAMETERS=
CFLAGS=
LDFLAGS=
GDB="false"
LIBRARIES_FOLDER="libraries"
DIFFTEST="false"
DIFFTEST_FOLDER="difftest"
DIFFTEST_PATH=$LIBRARIES_FOLDER/$DIFFTEST_FOLDER
DIFFTEST_TOP_FILE="SimTop.v"
NEMU_PATH=$LIBRARIES_FOLDER"/NEMU"
DIFFTEST_HELPER_PATH="src/test/vsrc/common"
DIFFTEST_PARAM=
TEST_CASES="false"
DRAMSIM3_FOLDER="libraries/DRAMsim3"
TEST_CASES=

# Check parameters
while getopts 'he:bt:sa:f:l:gwcdm:r:' OPT; do
    case $OPT in
        h) help;;
        e) PROJECT_FOLDER="$OPTARG";;
        b) BUILD="true";;
        t) V_TOP_FILE="$OPTARG";;
        s) SIMULATE="true";;
        a) PARAMETERS="$OPTARG";;
        f) CFLAGS="$OPTARG";;
        l) LDFLAGS="$OPTARG";;
        g) GDB="true";;
        w) CHECK_WAVE="true";;
        c) CLEAN="true";;
        d) DIFFTEST="true";;
        m) DIFFTEST_PARAM="$OPTARG";;
        r) TEST_CASES="$OPTARG"; DIFFTEST="true";;
        ?) help;;
    esac
done

[[ $LDFLAGS ]] && LDFLAGS="-LDFLAGS "\"$LDFLAGS\"

PROJECT_PATH=$OSCPU_PATH/projects/$PROJECT_FOLDER
[[ "$DIFFTEST" == "true" ]] && BUILD_PATH=$PROJECT_PATH/$DIFF_BUILD_FOLDER || BUILD_PATH=$PROJECT_PATH/$BUILD_FOLDER
[[ "$DIFFTEST" == "true" ]] && V_TOP_FILE=$DIFFTEST_TOP_FILE
NEMU_HOME=$OSCPU_PATH/$NEMU_PATH
DIFFTEST_HOME=$OSCPU_PATH/$DIFFTEST_PATH
DRAMSIM3_HOME=$OSCPU_PATH/$DRAMSIM3_FOLDER
LIBRARIES_HOME=$OSCPU_PATH/$LIBRARIES_FOLDER
export NEMU_HOME=$NEMU_HOME
export NOOP_HOME=$PROJECT_PATH
export DRAMSIM3_HOME=$DRAMSIM3_HOME

# Get id and name
ID=`sed '/^ID=/!d;s/.*=//' $MYINFO_FILE`
NAME=`sed '/^Name=/!d;s/.*=//' $MYINFO_FILE`
if [[ ${#ID} -le 7 ]] || [[ ${#NAME} -le 1 ]]; then
    echo "Please fill your information in myinfo.txt!!!"
    exit 1
fi
ID="${ID##*\r}"
NAME="${NAME##*\r}"

# Clean
if [[ "$CLEAN" == "true" ]]; then
    rm -rf $PROJECT_PATH/$BUILD_FOLDER $PROJECT_PATH/$DIFF_BUILD_FOLDER $PROJECT_PATH/out
    unlink $PROJECT_PATH/$DIFFTEST_FOLDER 1>/dev/null 2>&1
    exit 0
fi

# Build project
if [[ "$BUILD" == "true" ]]; then
    [[ "$DIFFTEST" == "true" ]] && build_diff_proj || build_proj

    #git commit
    # if [[ ! -f $OSCPU_PATH/.no_commit ]]; then
    #     git add . -A --ignore-errors
    #     (echo $NAME && echo $ID && hostnamectl && uptime) | git commit -F - -q --author='tracer-oscpu2021 <tracer@oscpu.org>' --no-verify --allow-empty 1>/dev/null 2>&1
    #     sync
    # fi
fi

# Simulate
if [[ "$SIMULATE" == "true" ]]; then
    create_bin_soft_link

    cd $BUILD_PATH
    
    # run simulation program
    echo "Simulating..."
    [[ "$GDB" == "true" ]] && gdb -s $EMU_FILE --args ./$EMU_FILE $PARAMETERS || ./$EMU_FILE $PARAMETERS

    if [ $? -ne 0 ]; then
        echo "Failed to simulate!!!"
        FAILED="true"
    fi

    cd $OSCPU_PATH
fi

# Check waveform
if [[ "$CHECK_WAVE" == "true" ]]; then
    cd $BUILD_PATH
    gtkwave `ls -t | grep .vcd | head -n 1`
    if [ $? -ne 0 ]; then
        echo "Failed to run gtkwave!!!"
        exit 1
    fi
    cd $OSCPU_PATH
fi

[[ "$FAILED" == "true" ]] && exit 1

# Run all
if [[ -n $TEST_CASES ]]; then
    create_bin_soft_link

    cd $BUILD_PATH

    mkdir log 1>/dev/null 2>&1
    for FOLDER in ${TEST_CASES[@]}
    do
        BIN_FILES=`eval "find $FOLDER -mindepth 1 -maxdepth 1 -regex \".*\.\(bin\)\""`
        for BIN_FILE in $BIN_FILES; do
            FILE_NAME=`basename ${BIN_FILE%.*}`
            printf "[%30s] " $FILE_NAME
            LOG_FILE=log/$FILE_NAME-log.txt
            ./$EMU_FILE -i $BIN_FILE &> $LOG_FILE
            if (grep 'HIT GOOD TRAP' $LOG_FILE > /dev/null) then
                echo -e "\033[1;32mPASS!\033[0m"
                rm $LOG_FILE
            else
                echo -e "\033[1;31mFAIL!\033[0m see $BUILD_PATH/$LOG_FILE for more information"
            fi
        done
    done

    cd $OSCPU_PATH
fi
