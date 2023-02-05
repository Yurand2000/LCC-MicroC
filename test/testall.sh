#!/bin/bash

# Check if clang is available otherwise abort
if ! command -v clang --version &> /dev/null
then
    echo "Cannot find clang compiler"
    exit
fi

# Make compile directory
if ! mkdir -p "$3"; then
    echo "Cannot create directory \"$3\""
    exit
fi

# Firstly Compile The Runtime Support with clang
RTIN="$4"
RTOUT="${RTIN##*/}"
RTOUT="$3/${RTOUT%.*}.o"
clang -c "$RTIN" -o "$RTOUT"

# Compile and check each file with its expected output
for file in $2*; do
    if [[ "$file" == */test-*.mc ]]; then
        echo -ne "                                             \r";
        echo -ne "Compiling $file \r";
        if "$1" -dir "$3" -rt "$RTOUT" -o "$3/a.out" -O "$file" -verify; then
            FILE="${file%.*}.out"
            if [[ -f "$FILE" ]]; then
                echo -ne "                                             \r";
                echo -ne "Testing $file\r";
                "$3/a.out" | diff - "${file%.*}.out";
            else
                echo "Output file for test \"$file\" not found...";
            fi
        else
            echo "File \"$file\" failed to compile. "
        fi
    fi
done

echo -ne "                                             \r";