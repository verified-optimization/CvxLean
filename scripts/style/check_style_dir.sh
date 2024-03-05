#!/bin/bash

DIR="$1"

if [ ! -d "$DIR" ]; then
    echo "Directory $directory does not exist."
    exit 1
fi

for file in "$DIR"/*.lean; do
    if [ -f "$file" ]; then
        ./scripts/style/check_style_file.sh "$file"
    fi
done
