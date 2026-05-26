CC ?= cc
CFLAGS ?= -std=c11 -Wall -Wextra -pedantic -mbmi2

TARGET = perfect
SRC = perfect.c

.PHONY: all clean test

all: $(TARGET)

$(TARGET): $(SRC)
	$(CC) $(CFLAGS) $(SRC) -o $(TARGET)

test: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(TARGET)
