BUILD_DIR=/build
CLANG=/usr/bin/clang

default_target: \
	$(BUILD_DIR)/as-hello $(BUILD_DIR)/as-cat

$(BUILD_DIR)/as-%.o : %.s
	$(CLANG) --verbose -target x86_64 -c $< -o $@

$(BUILD_DIR)/as-hello : $(BUILD_DIR)/as-hello-main.o $(BUILD_DIR)/as-hello-module.o
	ld -o $(BUILD_DIR)/as-hello $(BUILD_DIR)/as-hello-main.o $(BUILD_DIR)/as-hello-module.o

$(BUILD_DIR)/as-cat : $(BUILD_DIR)/as-cat.o
	ld -o $(BUILD_DIR)/as-cat $(BUILD_DIR)/as-cat.o

.SUFFIXES:
