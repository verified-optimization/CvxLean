#!/bin/bash

DIR="$1"

if [ ! -d "$DIR" ]; then
    echo "Directory $directory does not exist."
    exit 1
fi

find "$DIR" -type f -name "*.lean" -print0 | while IFS= read -r -d '' file; do
    if [ -f "$file" ]; then
        echo "Checking style for file $file"
        ./scripts/style/check_style_file.sh "$file" 2>&1
    fi
done
